open Util

type 'a t = {
  id : int;
  name : string; (* name must be normalized by [normalize_name] *)
  typ : 'a;
  attr : attr list;
}

and attr = External | Coefficient | Predicate | Primitive [@@deriving show]

let init_counter = 0
let counter = ref init_counter
let tmp_counter = ref init_counter

let new_int () =
  incr counter;
  !counter

let get_counter () = !counter
let set_counter n = counter := n
let save_counter () = tmp_counter := !counter
let reset_counter () = set_counter !tmp_counter
let clear_counter () = set_counter init_counter

let normalize_name s =
  if s.[0] = '(' then s
  else
    let first = s.[0] in
    let last = String.last s in
    if List.mem '*' [ first; last ] then "( " ^ s ^ " )"
    else if Char.is_symbol last then "(" ^ s ^ ")"
    else s

let make ?(id = 0) ?(attr = []) name typ =
  assert (name <> "");
  let name = normalize_name name in
  { id; name; attr; typ }

let new_var ?(name = "x") ?(attr = []) typ = make ~id:(new_int ()) name ~attr typ

let new_coeff ?(name = "c") ?(attr = []) typ =
  make ~id:(new_int ()) name ~attr:(Coefficient :: attr) typ

let new_predicate ?(name = "p") ?(attr = []) typ =
  make ~id:(new_int ()) name ~attr:(Predicate :: attr) typ

let new_var_id x = { x with id = new_int () }
let id x = x.id
let name x = x.name
let typ x = x.typ
let attr x = x.attr
let is_external x = List.mem External x.attr
let is_coefficient x = List.mem Coefficient x.attr
let is_predicate x = List.mem Predicate x.attr
let is_primitive x = List.mem Primitive x.attr

let to_string ?(plain = true) x =
  let s =
    let n = id x in
    if n <= 0 then name x else name x ^ "_" ^ string_of_int n
  in
  if plain then s
  else
    let s = if is_coefficient x then "#" ^ s else s in
    let s = if is_predicate x then "|" ^ s ^ "|" else s in
    s

let of_string name typ =
  let name = if name = "" then "x" else name in
  let attr = [] in
  let name, attr =
    if name.[0] = '#' then (String.lchop name, Coefficient :: attr) else (name, attr)
  in
  let name, attr =
    if name.[0] = '$' && String.length name >= 3 && String.last name = '$' then
      (String.chop name, Predicate :: attr)
    else (name, attr)
  in
  try
    let s1, s2 = String.rsplit name ~by:"_" in
    { id = int_of_string s2; name = s1; typ; attr }
  with _ -> { id = 0; name; typ; attr }

let compare { id = id_x; name = name_x } { id = id_y; name = name_y } =
  let r = id_x - id_y in
  if r <> 0 then r else compare name_x name_y

let eq { id = id_x; name = name_x } { id = id_y; name = name_y } = id_x = id_y && name_x = name_y
let same = eq
let equal = eq
let eq_ty ?(eq = ( = )) x y = same x y && eq (typ x) (typ y)
let set_id x id = { x with id }
let set_name x name = { x with name }
let set_typ x typ = { x with typ }
let set_attr x attr = { x with attr }
let add_name_before str x = set_name x (str ^ name x)
let add_name_after str x = set_name x (name x ^ str)
let add_name_prefix = add_name_before
let add_name_postfix = add_name_after
let add_name_suffix = add_name_after
let add_attr attr x = { x with attr = List.cons_unique attr x.attr }
let map_id f x = { x with id = f x.id }
let map_name f x = { x with name = f x.name }
let map_typ f x = { x with typ = f x.typ }
let map_attr f x = { x with attr = f x.attr }
let print_as_ocaml = ref false
let set_print_as_ocaml () = print_as_ocaml := true
let tmp_set_print_as_ocaml f = Ref.tmp_set print_as_ocaml true f

let print fm x =
  let s = to_string ~plain:false x in
  assert (s <> "");
  let s = if !print_as_ocaml then String.sign_to_letters @@ String.uncapitalize_ascii s else s in
  Format.pp_print_string fm s

let prefix_for_module m = name m ^ "."
let add_module_prefix_string ~m s = prefix_for_module m ^ s
let add_module_prefix ~m x = add_name_before (prefix_for_module m) x
let is_in_module_string ~m s = String.starts_with s (prefix_for_module m)
let is_in_module ~m x = is_in_module_string ~m (name x)

let remove_module_prefix_string ?m s =
  match m with
  | None -> snd @@ String.split s ~by:"."
  | Some m ->
      if is_in_module_string ~m s then String.lchop ~n:(1 + String.length (name m)) s
      else invalid_arg "Id.remove_module_prefix_string"

let remove_module_prefix ?m x = map_name (remove_module_prefix_string ?m) x

let rename_module ?m_before ~m_after x =
  x |> remove_module_prefix ?m:m_before |> add_module_prefix ~m:m_after

let rename_module_string ?m_before ~m_after s =
  s |> remove_module_prefix_string ?m:m_before |> add_module_prefix_string ~m:m_after

let rec decomp_prefixes_string s =
  try
    if Char.is_uppercase s.[0] then
      let prefix, s' = String.split s ~by:"." in
      let prefixes, s'' = decomp_prefixes_string s' in
      (prefix :: prefixes, s'')
    else ([], s)
  with Not_found -> ([], s)

let decomp_prefixes dummy_ty x =
  let prefixes, name = decomp_prefixes_string (name x) in
  (List.map (make -$- dummy_ty) prefixes, set_name x name)

module List = List.Make (struct
  type nonrec 'a t = 'a t

  let eq = eq
end)

(*** DO NOT ADD FUNCTIONS BELOW THIS LINE ***)

let ( = ) = same
let ( <> ) x y = not (same x y)
