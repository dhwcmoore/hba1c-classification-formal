#!/bin/bash
set -e

GREEN="\033[0;32m"
YELLOW="\033[1;33m"
NC="\033[0m"

TODAY=$(date +%Y%m%d)
OUTDIR="results/$TODAY"
mkdir -p "$OUTDIR"

GHB_URL="https://wwwn.cdc.gov/Nchs/Data/Nhanes/Public/2017/DataFiles/GHB_J.XPT"
BPX_URL="https://wwwn.cdc.gov/Nchs/Data/Nhanes/Public/2017/DataFiles/BPX_J.XPT"
TCHOL_URL="https://wwwn.cdc.gov/Nchs/Data/Nhanes/Public/2017/DataFiles/TCHOL_J.XPT"
DEMO_URL="https://wwwn.cdc.gov/Nchs/Data/Nhanes/Public/2017/DataFiles/DEMO_J.XPT"

cleanup() {
  rm -f GHB_J.XPT BPX_J.XPT TCHOL_J.XPT DEMO_J.XPT
}
trap cleanup EXIT

download_xpt() {
  echo -e "${YELLOW}Downloading NHANES files...${NC}"
  wget -q -O GHB_J.XPT "$GHB_URL"
  wget -q -O BPX_J.XPT "$BPX_URL"
  wget -q -O TCHOL_J.XPT "$TCHOL_URL"
  wget -q -O DEMO_J.XPT "$DEMO_URL"
  echo -e "${GREEN}✓ Download complete${NC}"
}

validate_xpt_or_retry() {
  local file="$1"
  local label="$2"
  if ! head -n 1 "$file" | grep -q "HEADER RECORD"; then
    echo -e "${YELLOW}Invalid $label format. Showing first 5 lines for debug:${NC}"
    head -n 5 "$file"
    echo -e "${YELLOW}Retrying download...${NC}"
    wget -q -O "$file" "${!label}_URL"
    if ! head -n 1 "$file" | grep -q "HEADER RECORD"; then
      echo -e "${YELLOW}Still invalid. Exiting.${NC}"
      exit 1
    fi
  fi
  echo -e "${GREEN}✓ $label format validated${NC}"
}

extract_csv() {
  echo -e "${YELLOW}Running Python extraction...${NC}"
  python3 <<EOF
import pandas as pd

ghb = pd.read_sas("GHB_J.XPT")
bpx = pd.read_sas("BPX_J.XPT")
tchol = pd.read_sas("TCHOL_J.XPT")
demo = pd.read_sas("DEMO_J.XPT")

ghb[["SEQN", "LBXGH"]].dropna().to_csv("$OUTDIR/nhanes_hba1c.csv", index=False)
bpx[["SEQN", "BPXSY1","BPXDI1","BPXSY2","BPXDI2","BPXSY3","BPXDI3"]].to_csv("$OUTDIR/nhanes_bp.csv", index=False)
tchol[["SEQN", "LBXTC"]].dropna().to_csv("$OUTDIR/nhanes_cholesterol.csv", index=False)
demo[["SEQN", "RIDAGEYR", "RIAGENDR"]].to_csv("$OUTDIR/nhanes_demo.csv", index=False)
EOF
  echo -e "${GREEN}✓ CSV extraction complete${NC}"
}

classify_verified() {
  echo -e "${YELLOW}Running formal classification...${NC}"
  dune exec ocaml/main_nhanes.exe process "$OUTDIR/nhanes_hba1c.csv" "$OUTDIR/nhanes_bp.csv" > "$OUTDIR/classification.log"
  echo -e "${GREEN}✓ Classification complete${NC}"
}

summarize_results() {
  echo -e "${YELLOW}Generating summary report...${NC}"
  python3 scripts/summarize_results.py "$OUTDIR"
  echo -e "${GREEN}✓ Summary written to $OUTDIR/summary.txt${NC}"
}

# Execute steps
download_xpt
validate_xpt_or_retry GHB_J.XPT GHB_J
validate_xpt_or_retry BPX_J.XPT BPX_J
validate_xpt_or_retry TCHOL_J.XPT TCHOL_J
validate_xpt_or_retry DEMO_J.XPT DEMO_J
extract_csv
classify_verified
summarize_results

echo -e "${GREEN}🎯 All done. Verified results are in $OUTDIR${NC}"
