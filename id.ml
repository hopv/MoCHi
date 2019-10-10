open Util

type 'a t =
  {id : int;
   name : string;
   typ : 'a;
   attr : attr list}

and attr =
  | External
  | Coefficient
  | Predicate
  | Module
  [@@deriving show]

let init_counter = 0
let counter = ref init_counter
let tmp_counter = ref init_counter

let new_int () = incr counter; !counter
let get_counter () = !counter
let set_counter n = counter := n
let save_counter () = tmp_counter := !counter
let reset_counter () = set_counter !tmp_counter
let clear_counter () = set_counter init_counter

let make id name attr typ = {id; name; attr; typ}
let new_var ?(name="x") ?(attr=[]) typ = make (new_int()) name attr typ
let new_coeff ?(name="c") ?(attr=[]) typ = make (new_int()) name (Coefficient::attr) typ
let new_predicate ?(name="p") ?(attr=[]) typ = make (new_int()) name (Predicate::attr) typ
let new_var_id x = {x with id=new_int()}

let id x = x.id
let name x = x.name
let typ x = x.typ
let attr x = x.attr

let is_external x = List.mem External x.attr
let is_coefficient x = List.mem Coefficient x.attr
let is_predicate x = List.mem Predicate x.attr
let is_module x = List.mem Module x.attr

let to_string ?(plain=true) x =
  let s =
    let n = id x in
    if n <= 0 then
      name x
    else
      name x ^ "_" ^ string_of_int n
  in
  if plain then
    s
  else if s <> "" && s.[0] = '@' then (* for modular? *)
    "$" ^ String.sub s 1 (String.length s - 1) ^ "$"
  else
    let s = if is_coefficient x then "#" ^ s else s in
    let s = if is_external x then "$" ^ s else s in
    let s = if is_predicate x then "|" ^ s ^ "|" else s in
    s

let from_string name typ =
  let name = if name = "" then "x" else name in
  let attr = [] in
  let name,attr = if name.[0] = '#' then String.lchop name, Coefficient::attr else name, attr in
  let name,attr = if name.[0] = '$' then String.lchop name, External::attr else name, attr in
  let name,attr = if name.[0] = '$' && String.length name >= 3 && String.right name 1 = "$" then String.chop name, Predicate::attr else name, attr in
  try
    let s1,s2 = String.rsplit name "_" in
    {id=int_of_string s2; name=s1; typ=typ; attr}
  with _ -> {id=0; name; typ; attr}

let compare x y = Compare.on (Pair.make id name) x y
let eq x y = compare x y = 0
let same = eq

let set_id x id = {x with id}
let set_name x name = {x with name}
let set_typ x typ = {x with typ}

let add_name_before str x = set_name x (str ^ name x)
let add_name_after str x = set_name x (name x ^ str)

let add_attr attr x = {x with attr=attr::x.attr}

let mem x xs = List.mem ~eq x xs
let assoc x xs = List.assoc ~eq x xs
let mem_assoc x xs = List.mem_assoc ~eq x xs
let assoc_option x xs = List.assoc_option ~eq x xs

let map_id f x = {x with id = f x.id}
let map_name f x = {x with name = f x.name}
let map_typ f x = {x with typ = f x.typ}
let map_attr f x = {x with attr = f x.attr}

let print_as_ocaml = ref false
let set_print_as_ocaml () = print_as_ocaml := true
let tmp_set_print_as_ocaml f = Ref.tmp_set print_as_ocaml true f

let print fm x =
  let s = to_string ~plain:false x in
  assert (s <> "");
  let s =
    if !print_as_ocaml then
      String.sign_to_letters @@ String.uncapitalize s
    else
      s
  in
  Format.pp_print_string fm s

let prefix_for_module m = name m ^ "."
let add_module_prefix_to_string m s = prefix_for_module m ^ s
let add_module_prefix x ~m = add_name_before (prefix_for_module m) x
let is_in_module_string x s = String.starts_with (prefix_for_module x) s
let is_in_module x m = is_in_module_string x (name m)
let rename_module x y =
  name x
  |> String.lchop ~n:(String.length @@ prefix_for_module y)
  |> add_module_prefix_to_string y
  |> set_name x


let (=) = same
let (<>) x y = not (same x y)
