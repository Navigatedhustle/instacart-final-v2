
import os, json, re, math, urllib.parse, io, datetime, uuid
from collections import defaultdict
from flask import Flask, render_template, request
from reportlab.lib.pagesizes import letter
from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, Table, TableStyle
from reportlab.lib import colors
import config

app = Flask(__name__)

# --- Allow GHL iframe embedding (kept as-is if you already added it) ---
@app.after_request
def allow_ghl_embed(resp):
    try:
        resp.headers.pop('X-Frame-Options', None)
    except Exception:
        pass
    allowed_ancestors = (
        "frame-ancestors 'self' "
        "https://*.gohighlevel.com https://*.myhighlevel.com "
        "https://*.hlpages.com https://*.highlevel.com"
    )
    existing = resp.headers.get('Content-Security-Policy', '')
    if 'frame-ancestors' in existing:
        import re as _re
        csp = _re.sub(r"frame-ancestors [^;]*;?\\s*", "", existing).strip()
        if csp and not csp.endswith(";"):
            csp += "; "
        resp.headers['Content-Security-Policy'] = csp + allowed_ancestors
    else:
        resp.headers['Content-Security-Policy'] = allowed_ancestors
    resp.headers['X-Frame-Options'] = 'ALLOWALL'
    return resp

# ---------------- helpers ----------------
def clean_query(name: str):
    name = re.sub(r"[^A-Za-z0-9 ]+", " ", name).strip().lower()
    name = re.sub(r"\\s+", " ", name)
    return urllib.parse.quote_plus(name)

def instacart_search_url(query: str):
    q = clean_query(query)
    sid = uuid.uuid4()
    pvid = uuid.uuid4()
    return f"https://www.instacart.com/store/s?k={q}&search_id={sid}&page_view_id={pvid}&utm_campaign={urllib.parse.quote_plus(getattr(config,'UTM_CAMPAIGN','corporate-cut'))}"

def load_catalog():
    with open(os.path.join("data","catalog.json"),"r") as f:
        return json.load(f)

def tdee_from_goal(goal, bodyweight):
    mult = {"Fat loss": 11, "Recomp": 12, "Maintenance": 14}.get(goal, 12)
    return int(bodyweight * mult)

def low_carb_ok(obj, max_c=20, is_recipe=False):
    C = obj["macros"]["C"]
    if is_recipe:
        return C <= max_c*2
    return C <= max_c

# ---------------- selection ----------------
def score_item(item, per_meal_k):
    P = max(1, item["macros"]["P"])
    ppd = float(item["price"]) / max(1e-6,(P/25.0))
    return abs(item["macros"]["K"] - per_meal_k) * 0.55 + ppd * 0.45

def choose_items(catalog, total_meals, time_per_cook, per_meal_k, low_carb=False):
    rte = list(catalog["rte"])
    recipes = list(catalog["recipes"])
    if low_carb:
        rte = [r for r in rte if low_carb_ok(r, 20, False)]
        recipes = [r for r in recipes if low_carb_ok(r, 40, True)]
    rte.sort(key=lambda x: score_item(x, per_meal_k))
    recipes.sort(key=lambda r: abs(r["macros"]["K"] - per_meal_k))

    ratio = 0.6 if int(time_per_cook) > 10 else 0.75
    target_rte = int(total_meals * ratio)
    out = []
    i=j=0
    guard=0
    while len(out) < total_meals and guard < 10000:
        guard += 1
        made=False
        need_rte = (len([x for x in out if x["type"]=="rte"]) < target_rte)
        if (need_rte or j>=len(recipes)) and i < len(rte):
            out.append({"type":"rte","ref":rte[i]}); i+=1; made=True
        elif j < len(recipes):
            out.append({"type":"recipe","ref":recipes[j]}); j+=1; made=True
        if not made: break

    k=0
    while len(out) < total_meals and (rte or recipes) and k < 1000:
        k+=1
        if rte and (k%2==0):
            out.append({"type":"rte","ref":rte[k%len(rte)]})
        elif recipes:
            out.append({"type":"recipe","ref":recipes[k%len(recipes)]})
        else:
            break
    return out

def build_week_plan(chosen, meals_per_day, days, per_meal_target_k, catalog, low_carb=False):
    side_pool = sorted(
        [i for i in catalog["rte"] if (60<=i["macros"]["K"]<=350) and (low_carb_ok(i, 20) if low_carb else True)],
        key=lambda x: x["macros"]["K"]
    )
    days_plan = []
    idx=0
    extras=[]
    for d in range(days):
        meals=[]
        for m in range(meals_per_day):
            if idx>=len(chosen): break
            it = chosen[idx]; idx+=1
            if it["type"]=="rte":
                title = it["ref"]["name"]; macros = it["ref"]["macros"].copy()
            else:
                title = it["ref"]["title"]; macros = it["ref"]["macros"].copy()

            tries=0
            for s in side_pool:
                if tries>6: break
                if macros["K"]>=per_meal_target_k-30: break
                if macros["K"] + s["macros"]["K"] <= per_meal_target_k + 200:
                    for k in ("P","C","F","K"): macros[k]+=s["macros"][k]
                    title += " + " + s["name"]
                    extras.append({"type":"rte","ref":s,"day":d,"meal":len(meals)})
                    tries+=1
            meals.append({"title":title,"macros":macros})
        days_plan.append({"meals":meals,"total_protein":sum(m["macros"]["P"] for m in meals),"total_calories":sum(m["macros"]["K"] for m in meals)})
    return days_plan, extras

def add_item_to_lightest(day, item, extra_items, day_index):
    m_idx = min(range(len(day["meals"])), key=lambda i: day["meals"][i]["macros"]["K"])
    meal = day["meals"][m_idx]
    for k in ("P","C","F","K"): meal["macros"][k]+=item["macros"][k]
    extra_items.append({"type":"rte","ref":item,"day":day_index,"meal":m_idx})

def day_penalty(P,C,F,K, target_K, target_P, shares, protein_cap=None):
    if K==0: return 1e9
    p_pct=(P*4)/K; c_pct=(C*4)/K; f_pct=(F*9)/K
    kcal_band = abs(K - target_K) / target_K
    prot_floor = max(0, (target_P - P)/max(1,target_P))
    shares_pen = (abs(p_pct-shares["P"]), abs(c_pct-shares["C"]), abs(f_pct-shares["F"]))
    over_cap_pen = 0.0
    if protein_cap is not None and P > protein_cap:
        over_cap_pen = (P - protein_cap) / max(1, protein_cap) * 8.0  # strong penalty
    return kcal_band*3 + prot_floor*4 + sum(shares_pen) + over_cap_pen

def macro_gap(P,C,F,K, shares, protein_target, protein_cap):
    if K==0: return "P"
    p_now = (P*4)/K; c_now = (C*4)/K; f_now = (F*9)/K
    diffs = {"P":shares["P"] - p_now, "C":shares["C"] - c_now, "F":shares["F"] - f_now}
    if P >= protein_target:
        diffs["P"] = -1e9
    if P > protein_cap:
        diffs["P"] = -1e12
    return max(diffs, key=lambda k: diffs[k])

def balance_macros_for_week(plan_days, target, catalog, extra_items, low_carb=False):
    boosters = [i for i in catalog["rte"] if i["macros"]["P"]>=25 and i["macros"]["K"]<=230]
    carb_fillers = [i for i in catalog["rte"] if i["macros"]["C"]>=25]
    fat_fillers  = [i for i in catalog["rte"] if i["macros"]["F"]>=10]
    balanced_fillers = [i for i in catalog["rte"] if 12<=i["macros"]["P"]<=24 and 15<=i["macros"]["C"]<=35]
    micro = [i for i in catalog["rte"] if i["macros"]["K"]<=120]
    candidates = boosters + carb_fillers + fat_fillers + balanced_fillers + micro
    if low_carb:
        candidates = [c for c in candidates if low_carb_ok(c, 20)]

    target_K = int(target["calories"])
    protein_target = int(target["protein_g"])
    protein_cap    = int(target.get("protein_cap", protein_target))
    shares = target["shares"]

    def totals(day):
        P=sum(m["macros"]["P"] for m in day["meals"])
        C=sum(m["macros"]["C"] for m in day["meals"])
        F=sum(m["macros"]["F"] for m in day["meals"])
        K=sum(m["macros"]["K"] for m in day["meals"])
        return P,C,F,K

    for d_i, day in enumerate(plan_days):
        for _ in range(160):
            P,C,F,K = totals(day)
            lower, upper = target_K*0.95, target_K*1.05

            if P > protein_cap and extra_items:
                cands=[ex for ex in extra_items if ex.get("day")==d_i]
                if cands:
                    ex=max(cands, key=lambda e:e["ref"]["macros"]["P"])
                    m_idx=ex.get("meal",0)
                    meal=day["meals"][m_idx]
                    for k2 in ("P","C","F","K"):
                        meal["macros"][k2]=max(0, meal["macros"][k2]-ex["ref"]["macros"][k2])
                    extra_items.remove(ex)
                    continue

            if lower <= K <= upper and P>=protein_target:
                p_pct=(P*4)/K; c_pct=(C*4)/K; f_pct=(F*9)/K
                if (abs(p_pct-shares["P"])<=0.04 and abs(c_pct-shares["C"])<=0.04 and abs(f_pct-shares["F"])<=0.04 and P <= protein_cap):
                    break

            if K>upper and extra_items:
                cands=[ex for ex in extra_items if ex.get("day")==d_i]
                if cands:
                    ex=max(cands, key=lambda e:e["ref"]["macros"]["K"])
                    m_idx=ex.get("meal",0)
                    meal=day["meals"][m_idx]
                    for k2 in ("P","C","F","K"):
                        meal["macros"][k2]=max(0, meal["macros"][k2]-ex["ref"]["macros"][k2])
                    extra_items.remove(ex)
                    continue
                else:
                    break

            gap = macro_gap(P,C,F,K, shares, protein_target, protein_cap)
            if gap=="P" and P >= protein_target:
                gap = "C" if (shares["C"] - (C*4)/K) > (shares["F"] - (F*9)/K) else "F"

            pool = boosters if gap=="P" else (carb_fillers if gap=="C" else fat_fillers)
            if low_carb and gap=="C":
                pool = [i for i in balanced_fillers if i["macros"]["C"]<=18] + [i for i in micro if i["macros"]["C"]<=10]
            margin = target_K - K
            best=None; best_pen=1e18
            for cand in pool + candidates:
                if gap!="P" and cand in boosters and P >= protein_target:
                    continue
                if low_carb and not low_carb_ok(cand, 20):
                    continue
                if cand["macros"]["K"] > min(350, margin+200):
                    continue
                P2, C2, F2, K2 = P+cand["macros"]["P"], C+cand["macros"]["C"], F+cand["macros"]["F"], K+cand["macros"]["K"]
                pen = day_penalty(P2,C2,F2,K2, target_K, protein_target, shares, protein_cap=protein_cap)
                if pen < best_pen:
                    best_pen = pen; best = cand
            if best:
                add_item_to_lightest(day, best, extra_items, d_i)
                continue

            break

        day["total_protein"]=sum(m["macros"]["P"] for m in day["meals"])
        day["total_calories"]=sum(m["macros"]["K"] for m in day["meals"])
    return plan_days, extra_items

def item_price(it):
    return float(it["ref"]["price"] if it["type"]=="rte" else it["ref"]["price_per_serv"])

def cheap_fillers(catalog, low_carb=False):
    fillers = [x for x in catalog["rte"] if x["macros"]["K"]>=60]
    if low_carb:
        fillers = [x for x in fillers if low_carb_ok(x, 20)]
    return sorted(fillers, key=lambda r: (r["price"]/max(1,r["macros"]["K"])))

def top_up_days_with_budget(days_plan, extras, catalog, target, current_cost, budget, low_carb=False):
    fillers = cheap_fillers(catalog, low_carb)
    target_K = int(target["calories"]); lower = target_K*0.95
    headroom = max(0.0, budget - current_cost)

    def day_totals(d):
        K=sum(m["macros"]["K"] for m in d["meals"])
        P=sum(m["macros"]["P"] for m in d["meals"])
        C=sum(m["macros"]["C"] for m in d["meals"]); F=sum(m["macros"]["F"] for m in d["meals"])
        return P,C,F,K

    changed=True
    while headroom > 0.25 and changed:
        changed=False
        deficits=[(i, day_totals(d)[3]) for i,d in enumerate(days_plan)]
        i_min, k_min = min(deficits, key=lambda t: t[1])
        if k_min >= lower: break
        day = days_plan[i_min]
        P,C,F,K = day_totals(day)
        best=None; best_score=-1
        for cand in fillers:
            price=cand["price"]
            if price>headroom: continue
            P2,C2,F2,K2 = P+cand["macros"]["P"], C+cand["macros"]["C"], F+cand["macros"]["F"], K+cand["macros"]["K"]
            gain = min(target_K, K2) - K
            score = gain / max(0.01, price)
            if score>best_score:
                best=(cand, i_min); best_score=score
        if best:
            cand, di = best
            m_idx = min(range(len(day["meals"])), key=lambda mi: day["meals"][mi]["macros"]["K"])
            for k in ("P","C","F","K"): day["meals"][m_idx]["macros"][k]+=cand["macros"][k]
            extras.append({"type":"rte","ref":cand,"day":di,"meal":m_idx})
            headroom -= cand["price"]
            day["total_protein"]=sum(m["macros"]["P"] for m in day["meals"])
            day["total_calories"]=sum(m["macros"]["K"] for m in day["meals"])
            changed=True

    return days_plan, extras, headroom

# ---------------- groceries ----------------
def groceries_from_plan(base_items, extras, household=1):
    by_aisle=defaultdict(list); csv_rows=[]; queries=[]
    counter={}
    def add(name, aisle, package, price, P, K, query):
        key=(name,aisle,package)
        counter[key]=counter.get(key,0)+household
        queries.append(query)

    for ch in base_items:
        if ch["type"]=="rte":
            r=ch["ref"]; add(r["name"], r["aisle"], r["package"], r["price"], r["macros"]["P"], r["macros"]["K"], r.get("insta_query", r["name"]))
        else:
            r=ch["ref"]
            for ing in r["ingredients"][:4]:
                add(f"{ing} ({r['title']})", r.get("aisles",["Center Aisle"])[0], "varies", r["price_per_serv"]/2, r["macros"]["P"], r["macros"]["K"], ing)

    for ex in extras:
        r=ex["ref"]; add(r["name"], r["aisle"], r["package"], r["price"], r["macros"]["P"], r["macros"]["K"], r.get("insta_query", r["name"]))

    for (name,aisle,package),qty in counter.items():
        by_aisle[aisle].append({"name":name,"package":package,"instacart_url":instacart_search_url(name)})
        csv_rows.append({"name":name,"aisle":aisle,"qty":qty,"unit":package})
    return by_aisle, csv_rows, "\\n".join(queries)

# ---------------- globals ----------------
LAST_META={}
LAST_DAYS=[]
LAST_CSV=[]
LAST_GROCERY={}
LAST_BASE=[]
LAST_EXTRAS=[]
LAST_COST=0.0
LAST_PREFS={}

# ---------------- routes ----------------
@app.route("/")
def index():
    return render_template("index.html", APP_NAME=config.APP_NAME, BRAND_NAME=config.BRAND_NAME, FAVICON=config.FAVICON, ACCENT=getattr(config, "ACCENT", "#f97316"), now=datetime.datetime.utcnow())

@app.route("/plan", methods=["POST"])
def plan():
    goal=request.form.get("goal","Fat loss")
    bodyweight=int(request.form.get("bodyweight","185"))
    calories_str=request.form.get("calories","").strip()
    meals_per_day=int(request.form.get("meals_per_day","4"))
    budget=float(request.form.get("budget","180"))
    time_per_cook=int(request.form.get("time_per_cook","10"))
    low_carb = request.form.get("low_carb") == "on"
    days=7

    shares = {"P":0.45,"C":0.20,"F":0.35} if low_carb else {"P":0.40,"C":0.30,"F":0.30}
    calories=int(calories_str) if calories_str else tdee_from_goal(goal, bodyweight)

    # --- STRICT PROTEIN RULES ---
    protein_target = int(bodyweight)                 # 1.0 g/lb
    protein_cap    = int(math.ceil(bodyweight * 1.1))  # hard cap 1.1 g/lb (never exceed)
    fat_g=int(shares["F"]*calories/9)
    carb_g=int(shares["C"]*calories/4)
    target={"calories":calories,"protein_g":protein_target,"protein_cap":protein_cap,"fat_g":fat_g,"carb_g":carb_g,"shares":shares}

    per_meal_k=int(calories/meals_per_day)
    catalog=load_catalog()

    total_meals=meals_per_day*days
    chosen=choose_items(catalog, total_meals, time_per_cook, per_meal_k, low_carb)
    days_plan, extras=build_week_plan(chosen, meals_per_day, days, per_meal_k, catalog, low_carb)
    days_plan, extras=balance_macros_for_week(days_plan, target, catalog, extras, low_carb)

    cost=sum((item_price(it) for it in chosen)) + sum((e["ref"]["price"] for e in extras))
    if cost>budget:
        extras.sort(key=lambda e: float(e["ref"]["price"]), reverse=True)
        for ex in list(extras):
            if cost<=budget: break
            d=ex.get("day",0); m=ex.get("meal",0)
            if d<len(days_plan) and m<len(days_plan[d]["meals"]):
                meal=days_plan[d]["meals"][m]
                for k in ("P","C","F","K"):
                    meal["macros"][k]=max(0, meal["macros"][k]-ex["ref"]["macros"][k])
            cost-=float(ex["ref"]["price"]); extras.remove(ex)
        for d in days_plan:
            d["total_protein"]=sum(m["macros"]["P"] for m in d["meals"])
            d["total_calories"]=sum(m["macros"]["K"] for m in d["meals"])

    days_plan, extras, _ = top_up_days_with_budget(days_plan, extras, catalog, target, cost, budget, low_carb)
    days_plan, extras = balance_macros_for_week(days_plan, target, catalog, extras, low_carb)

    grocery, csv_rows, queries = groceries_from_plan(chosen, extras, household=1)
    total_cost = sum((item_price(it) for it in chosen)) + sum((e["ref"]["price"] for e in extras))

    global LAST_META, LAST_DAYS, LAST_CSV, LAST_GROCERY, LAST_BASE, LAST_EXTRAS, LAST_COST, LAST_PREFS
    LAST_META={"calories":calories,"protein_g":protein_target,"budget":budget}
    LAST_DAYS=days_plan
    LAST_CSV=csv_rows
    LAST_GROCERY=grocery
    LAST_BASE=chosen
    LAST_EXTRAS=extras
    LAST_COST=total_cost
    LAST_PREFS={"low_carb":low_carb}

    plan={
        "days":days_plan,"grocery":grocery,"csv_rows":csv_rows,"queries":queries,
        "total_cost":total_cost,"calories":calories,"protein_target":protein_target,"budget":budget,
        "low_carb":low_carb
    }
    return render_template("plan.html", plan=plan, APP_NAME=config.APP_NAME, BRAND_NAME=config.BRAND_NAME, FAVICON=config.FAVICON, ACCENT=getattr(config,"ACCENT","#f97316"), now=datetime.datetime.utcnow())

# -------- Exports --------
@app.route("/export/csv")
def export_csv():
    if not LAST_CSV: return "No plan generated", 400
    import csv
    buf=io.StringIO()
    w=csv.writer(buf)
    w.writerow(["Item","Aisle","Qty","Unit"])
    for r in LAST_CSV:
        w.writerow([r["name"], r["aisle"], r["qty"], r["unit"]])
    buf.seek(0)
    return app.response_class(buf.getvalue(), mimetype="text/csv", headers={"Content-Disposition":"attachment; filename=grocery.csv"})

def wrapped_paragraph(text, style):
    text = text.replace("&", "&amp;").replace("<","&lt;").replace(">","&gt;")
    return Paragraph(text, style)

def link_paragraph(url, text, style):
    return Paragraph(f'<link href="{url}">{text}</link>', style)

@app.route("/export/plan.pdf")
def export_plan_pdf():
    if not LAST_DAYS: return "No plan generated", 400
    buff=io.BytesIO()
    doc=SimpleDocTemplate(buff, pagesize=letter, title="Meal Plan", leftMargin=36, rightMargin=36, topMargin=36, bottomMargin=36)
    styles=getSampleStyleSheet()
    title = styles["Title"]; title.fontName="Helvetica-Bold"; title.fontSize=19
    h3 = styles["Heading3"]; h3.fontName="Helvetica-Bold"; h3.fontSize=12
    body = ParagraphStyle("body", parent=styles["Normal"], fontName="Helvetica", fontSize=10, leading=12, wordWrap='LTR')
    elems=[wrapped_paragraph("ActivBlaze Corporate Cut — 7-Day Plan", title),
           wrapped_paragraph(f"Calories/day target: {LAST_META.get('calories')} • Protein target: {LAST_META.get('protein_g')} g • Budget: ${LAST_META.get('budget')} • Diet: {'Low-carb' if LAST_PREFS.get('low_carb') else 'Standard 40/30/30'}", body),
           Spacer(1,10)]
    zebra=[colors.whitesmoke, colors.HexColor('#eef2ff')]
    for i, day in enumerate(LAST_DAYS, start=1):
        elems.append(wrapped_paragraph(f"Day {i} — {day.get('total_protein',0)} g protein, ~{int(day.get('total_calories',0))} kcal", h3))
        data=[["Meal","P","C","F","K"]]
        for m in day["meals"]:
            mc=m["macros"]
            data.append([wrapped_paragraph(m["title"], body), mc["P"], mc["C"], mc["F"], mc["K"]])
        t=Table(data, repeatRows=1, colWidths=[320,45,45,45,55])
        t.setStyle(TableStyle([
            ('FONT',(0,0),(-1,-1),'Helvetica'),
            ('BACKGROUND',(0,0),(-1,0),colors.black),
            ('TEXTCOLOR',(0,0),(-1,0),colors.white),
            ('VALIGN',(0,0),(-1,-1),'TOP'),
            ('ALIGN',(1,1),(-1,-1),'RIGHT'),
            ('GRID',(0,0),(-1,-1),0.25,colors.grey),
        ]))
        for r in range(1, len(data)):
            t.setStyle(TableStyle([('BACKGROUND',(0,r),(-1,r), zebra[r%2])]))
        elems.extend([t, Spacer(1,10)])
    doc.build(elems)
    pdf=buff.getvalue(); buff.close()
    return app.response_class(pdf, mimetype="application/pdf", headers={"Content-Disposition":"attachment; filename=plan.pdf"})

@app.route("/export/grocery.pdf")
def export_grocery_pdf():
    if not LAST_GROCERY: return "No plan generated", 400
    buff=io.BytesIO()
    doc=SimpleDocTemplate(buff, pagesize=letter, title="Grocery List", leftMargin=36, rightMargin=36, topMargin=36, bottomMargin=36)
    styles=getSampleStyleSheet()
    title = ParagraphStyle("t", parent=styles["Title"], fontName="Helvetica-Bold", fontSize=19)
    h3 = ParagraphStyle("h3", parent=styles["Heading3"], fontName="Helvetica-Bold", fontSize=12)
    body = ParagraphStyle("body", parent=styles["Normal"], fontName="Helvetica", fontSize=10, leading=12, wordWrap='LTR')
    elems=[wrapped_paragraph("ActivBlaze Corporate Cut — Grocery List", title), Spacer(1,8)]
    total=LAST_COST
    for aisle, items in LAST_GROCERY.items():
        elems.append(wrapped_paragraph(aisle, h3))
        data=[["Item","Package","Instacart"]]
        for it in items:
            data.append([wrapped_paragraph(it["name"], body), wrapped_paragraph(it["package"], body), link_paragraph(instacart_search_url(it["name"]), "Open in Instacart", body)])
        t=Table(data, repeatRows=1, colWidths=[300,100,160])
        t.setStyle(TableStyle([
            ('FONT',(0,0),(-1,-1),'Helvetica'),
            ('BACKGROUND',(0,0),(-1,0),colors.black),
            ('TEXTCOLOR',(0,0),(-1,0),colors.white),
            ('VALIGN',(0,0),(-1,-1),'TOP'),
            ('GRID',(0,0),(-1,-1),0.25,colors.grey),
        ]))
        for r in range(1, len(data)):
            t.setStyle(TableStyle([('BACKGROUND',(0,r),(-1,r), colors.whitesmoke if r%2==0 else colors.HexColor('#f1f5f9'))]))
        elems.extend([t, Spacer(1,6)])
    elems.append(wrapped_paragraph(f"Estimated Weekly Total: ${total:.2f}", h3))
    doc.build(elems)
    pdf=buff.getvalue(); buff.close()
    return app.response_class(pdf, mimetype="application/pdf", headers={"Content-Disposition":"attachment; filename=grocery.pdf"})

@app.route("/healthz")
def healthz():
    return "ok", 200

if __name__=="__main__":
    app.run(host="0.0.0.0", port=int(os.getenv("PORT", "5000")), debug=False)


