open Util

include Yojson.Basic

let load file of_json =
  let@ cin = IO.CPS.open_in file in
  cin
  |> IO.input_all
  |> from_string
  |> of_json

let save ?(pretty=false) file to_json data =
  let to_s json = if pretty then pretty_to_string json else to_string json in
  let@ cout = IO.CPS.open_out file in
  data
  |> to_json
  |> to_s
  |> output_string cout
