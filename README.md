# hba1c-classification-formal

Formal verification pipeline for classifying NHANES medical data — specifically glycohemoglobin (HbA1c), blood pressure, and cholesterol — with guarantees of mutual exclusion, threshold precision, and complete coverage.

---

## 🎯 Features

* ✅ **Formal Class Boundaries**: Verifies each sample belongs to *exactly one* class (e.g. diabetes, hypertension)
* ✅ **Complete Coverage**: Every subject is classified — no missing or overlapping cases
* ✅ **Stratified Analysis**: Gender/age-stratified plots with linear regression
* ✅ **Per-patient Audit Reports**: Auto-generated PDFs with class tags and visuals
* ✅ **Reproducible Pipeline**: Single-command execution (`./nhanes_pipeline.sh`)

---

## 📦 Inputs

| Source | File          | Description                |
| ------ | ------------- | -------------------------- |
| NHANES | `GHB_J.XPT`   | Glycohemoglobin (HbA1c)    |
| NHANES | `BPX_J.XPT`   | Blood Pressure             |
| NHANES | `TCHOL_J.XPT` | Total Cholesterol          |
| NHANES | `DEMO_J.XPT`  | Demographics (Age, Gender) |

---

## 🚀 Usage

```bash
# Clone repo and enter it
git clone https://github.com/dhwcmoore/hba1c-classification-formal.git
cd hba1c-classification-formal

# Set up Python virtualenv (if needed)
python3 -m venv venv
source venv/bin/activate
pip install -r requirements.txt

# Run pipeline
./nhanes_pipeline.sh
```

---

## 📊 Output Structure

```
results/YYYYMMDD/
├── summary.txt                  # Correlations and sample sizes
├── mutual_exclusion_check.txt  # Class overlap verification
├── chol_vs_sysbp.png           # Stratified regression
├── chol_vs_diabp.png
├── patient_audit.pdf           # PDF reports for 5 patients
```

---

## 📈 Example Output

* Systolic BP vs Cholesterol correlation: **0.225**
* Diastolic BP vs Cholesterol correlation: **0.231**
* Plots stratified by gender and age
* Class audit confirms **no overlaps** between hypertension and high-cholesterol labels

---

## ✅ Formal Guarantees

| Guarantee          | Description                                              |
| ------------------ | -------------------------------------------------------- |
| Mutual Exclusion   | No overlap between diagnostic classes                    |
| Boundary Precision | Thresholds (e.g. BP >= 130/80) strictly enforced         |
| Complete Coverage  | Every subject falls into exactly one class per condition |

---

## 📄 License

MIT License

---

## 🤝 Acknowledgments

* NHANES data (CDC)
* Verified extraction design by D. Moore
* Formalization inspired by AIQ case study

---

## 📬 Contact

[dhwcmoore@github](mailto:dhwcmoore@github)

