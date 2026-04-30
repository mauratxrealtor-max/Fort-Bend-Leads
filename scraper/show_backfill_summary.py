import json, sys
path = 'dashboard/backfill.json'
try:
    with open(path) as f:
        d = json.load(f)
    print(f"Backfill Total: {d['total']}")
    print(f"WithAddress: {d['with_address']}")
    print(f"HotLeads: {sum(1 for r in d['records'] if r.get('score',0) >= 70)}")
except Exception as e:
    print(f"Could not read {path}: {e}")
