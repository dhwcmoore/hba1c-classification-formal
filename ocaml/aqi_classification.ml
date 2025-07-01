(* OCaml version of classify_aqi *)

let classify_aqi aqi =
  if aqi < 50 then "Good"
  else if aqi < 100 then "Moderate"
  else if aqi < 150 then "Unhealthy for Sensitive Groups"
  else if aqi < 200 then "Unhealthy"
  else if aqi < 300 then "Very Unhealthy"
  else "Hazardous"
