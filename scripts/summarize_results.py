import pandas as pd
import seaborn as sns
import matplotlib.pyplot as plt
import sys
import os
from fpdf import FPDF

# CLI arg: output dir
outdir = sys.argv[1]

def load_data():
    df_bp = pd.read_csv(f"{outdir}/nhanes_bp.csv")
    df_chol = pd.read_csv(f"{outdir}/nhanes_cholesterol.csv")
    df_demo = pd.read_csv(f"{outdir}/nhanes_demo.csv")
    df = df_bp.merge(df_chol, on="SEQN").merge(df_demo, on="SEQN")
    df["SysBP"] = df[["BPXSY1", "BPXSY2", "BPXSY3"]].mean(axis=1, skipna=True)
    df["DiaBP"] = df[["BPXDI1", "BPXDI2", "BPXDI3"]].mean(axis=1, skipna=True)
    df = df.dropna(subset=["SysBP", "DiaBP", "LBXTC"])
    df["Gender"] = df["RIAGENDR"].map({1: "Male", 2: "Female"})
    return df

def plot_correlation(df, x, y, hue, filename):
    plt.figure(figsize=(8,6))
    sns.lmplot(x=x, y=y, hue=hue, data=df, aspect=1.5)
    plt.title(f"{y} vs {x} by {hue}")
    plt.savefig(f"{outdir}/{filename}")
    plt.close()

def compute_correlation(df):
    corr_sys = df[["SysBP", "LBXTC"]].corr().iloc[0,1]
    corr_dia = df[["DiaBP", "LBXTC"]].corr().iloc[0,1]
    with open(f"{outdir}/summary.txt", "w") as f:
        f.write(f"Correlation (Systolic vs Total Cholesterol): {corr_sys:.3f}\n")
        f.write(f"Correlation (Diastolic vs Total Cholesterol): {corr_dia:.3f}\n")

def generate_pdf(df):
    pdf = FPDF()
    pdf.add_page()
    pdf.set_font("Arial", size=12)
    pdf.cell(200, 10, txt="Top 5 Patients Summary", ln=True)

    for _, row in df.head(5).iterrows():
        pdf.cell(200, 10, txt=f"SEQN: {int(row['SEQN'])}, SysBP: {row['SysBP']:.1f}, DiaBP: {row['DiaBP']:.1f}, Chol: {row['LBXTC']:.1f}, Age: {int(row['RIDAGEYR'])}, Gender: {row['Gender']}", ln=True)

    pdf.output(f"{outdir}/patient_audit.pdf")

def verify_mutual_exclusion():
    log_file = f"{outdir}/classification.log"
    with open(log_file) as f:
        lines = f.readlines()

    dual_class = [line for line in lines if "MULTI_CLASS" in line]
    with open(f"{outdir}/mutual_exclusion_check.txt", "w") as f:
        if not dual_class:
            f.write("✓ All patient classifications are mutually exclusive.\n")
        else:
            f.write("⚠ Found patients in overlapping classes:\n")
            f.writelines(dual_class)

df = load_data()
plot_correlation(df, "LBXTC", "SysBP", "Gender", "chol_vs_sysbp.png")
plot_correlation(df, "LBXTC", "DiaBP", "Gender", "chol_vs_diabp.png")
compute_correlation(df)
generate_pdf(df)
verify_mutual_exclusion()
