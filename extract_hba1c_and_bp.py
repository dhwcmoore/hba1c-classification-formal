# extract_hba1c_and_bp.py
import pandas as pd

print("Converting your real NHANES data...")

try:
    # HbA1c data (Glycohemoglobin)
    ghb_data = pd.read_sas('GHB_J.XPT')
    print(f"✓ Loaded {len(ghb_data)} HbA1c records")

    clean_hba1c = ghb_data[['SEQN', 'LBXGH']].dropna()
    clean_hba1c.to_csv('nhanes_hba1c.csv', index=False)
    print(f"✓ Saved {len(clean_hba1c)} valid HbA1c records")

except Exception as e:
    print(f"GHB_J.XPT: {e}")

try:
    # Blood Pressure data
    bpx_data = pd.read_sas('BPX_J.XPT')
    print(f"✓ Loaded {len(bpx_data)} BP records")

    bp_cols = ['SEQN', 'BPXSY1', 'BPXDI1', 'BPXSY2', 'BPXDI2', 'BPXSY3', 'BPXDI3']
    clean_bp = bpx_data[bp_cols]
    clean_bp.to_csv('nhanes_bp.csv', index=False)
    print(f"✓ Saved {len(clean_bp)} BP records")

except Exception as e:
    print(f"BPX_J.XPT: {e}")

print("Ready for formal verification processing!")
