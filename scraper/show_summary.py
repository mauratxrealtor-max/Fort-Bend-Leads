import json
with open('dashboard/records.json') as f:
    d = json.load(f)
print(f"Total: {d['total']}  WithAddress: {d['with_address']}  HotLeads: {sum(1 for r in d['records'] if r.get('score',0) >= 70)}")
