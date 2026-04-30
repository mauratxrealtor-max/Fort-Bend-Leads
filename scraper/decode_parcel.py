import base64, os, sys
b64_path = 'data/parcel_compact.b64'
gz_path  = 'data/parcel_compact.csv.gz'
if not os.path.exists(b64_path):
    print('No parcel_compact.b64 found — skipping decode')
    sys.exit(0)
with open(b64_path, 'r') as f:
    raw = f.read().strip()
decoded = base64.b64decode(raw)
with open(gz_path, 'wb') as f:
    f.write(decoded)
print(f'Decoded parcel DB: {len(decoded):,} bytes -> {gz_path}')
