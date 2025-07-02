(* Simple NHANES Data Processing *)

let classify_diabetes_verified (hba1c : float) : string =
  if hba1c < 5.7 then "Normal"
  else if hba1c < 6.5 then "Prediabetes"  
  else "Diabetes"

let diabetes_clinical_action (classification : string) : string =
  match classification with
  | "Normal" -> "Continue routine screening every 3 years"
  | "Prediabetes" -> "Lifestyle intervention, retest in 1 year"
  | "Diabetes" -> "Immediate diabetes management protocol"
  | _ -> "Invalid measurement"

type boundary_proximity_alert = {
  input_value : float;
  nearest_boundary : float;
  distance : float;
  classification : string;
  confidence_level : [`High | `Medium | `Low];
}

let monitor_diabetes_boundary (hba1c : float) : boundary_proximity_alert option =
  let tolerance = 0.1 in
  let check_boundary threshold =
    let distance = abs_float (hba1c -. threshold) in
    if distance < tolerance then
      Some {
        input_value = hba1c;
        nearest_boundary = threshold;
        distance = distance;
        classification = classify_diabetes_verified hba1c;
        confidence_level = `High;
      }
    else None
  in
  
  match check_boundary 5.7 with
  | Some alert -> Some alert
  | None -> check_boundary 6.5

type bp_category = Normal | Elevated | Stage1_HTN | Stage2_HTN | Crisis | Invalid

let bp_category_to_string = function
  | Normal -> "Normal" 
  | Elevated -> "Elevated"
  | Stage1_HTN -> "Stage 1 Hypertension" 
  | Stage2_HTN -> "Stage 2 Hypertension"
  | Crisis -> "Hypertensive Crisis" 
  | Invalid -> "Invalid"

let classify_bp (systolic : float) (diastolic : float) : bp_category =
  if systolic >= 180.0 || diastolic >= 120.0 then Crisis
  else if systolic >= 140.0 || diastolic >= 90.0 then Stage2_HTN
  else if systolic >= 130.0 || diastolic >= 80.0 then Stage1_HTN
  else if systolic >= 120.0 then Elevated
  else Normal

let bp_clinical_action = function
  | Normal -> "Continue healthy lifestyle, recheck in 1 year"
  | Elevated -> "Lifestyle changes, recheck in 3-6 months"
  | Stage1_HTN -> "Lifestyle + medication, recheck in 1 month"
  | Stage2_HTN -> "Immediate medication + lifestyle, recheck in 1 week"
  | Crisis -> "🚨 EMERGENCY: Immediate medical attention required"
  | Invalid -> "Invalid measurement"

let process_nhanes_data (hba1c_file : string) (bp_file : string) : unit =
  Printf.printf "NHANES Real Data Processing\n";
  Printf.printf "===========================\n";
  Printf.printf "HbA1c file: %s\n" hba1c_file;
  Printf.printf "BP file: %s\n" bp_file;
  Printf.printf "Status: Ready for real data processing!\n"
