open Util
open Combinator

(** {6 Constructors} *)

type t =
  | V of string
  | C of string
  | T of t * int * int
  | N of int

(** {6 Printers} *)

let rec pr ppf x =
  match x with
  | V(id) -> String.pr ppf id
  | C(id) -> String.pr ppf id
  | T(x, uid, arg) -> Format.fprintf ppf "%a[%d:%d]" pr x uid arg
  (*"<%a@@%d:%d>"*)
  | N(n) -> Format.fprintf ppf "<%d>" n

let pr_list ppf xs = Format.fprintf ppf "@[<v>%a@]" (List.pr pr ",") xs

let rec pr_tex ppf x =
  match x with
  | V(id) -> String.pr ppf id
  | C(id) -> String.pr ppf id
  | T(x, uid, arg) -> Format.fprintf ppf "%a\\left[%d:%d\\right]" pr x uid arg
  (*"<%a@@%d:%d>"*)
  | N(n) -> Format.fprintf ppf "<%d>" n

(** {6 Auxiliary constructors} *)

let make id = V(id)
let mk_coeff id = C(id)

let new_var =
  let cnt = ref 0 in
  fun () ->
    incr cnt;
    V("var" ^ (string_of_int !cnt))

let new_list n = List.gen n (fun _ -> new_var ())

let new_vmap xs = List.map (fun x -> x, new_var ()) xs

let new_coeff =
  let cnt = ref 0 in
  fun ?(header = "_c") () ->
    incr cnt;
    C(header ^ (string_of_int !cnt))

let new_tvar =
  let cnt = ref 0 in
  fun () ->
    incr cnt;
    V("a" ^ (string_of_int !cnt))

let new_pvar =
  let cnt = ref 0 in
  fun () ->
    incr cnt;
    V("P" ^ (string_of_int !cnt))

let nu k = k (new_var ())

(** {6 Inspectors} *)

let equiv x y = x = y

let rec cong x1 x2 =
  match x1, x2 with
  | V(id1), V(id2) -> id1 = id2
  | T(x1, _, arg1), T(x2, _, arg2) -> arg1 = arg2 && cong x1 x2
  | _ -> false

let lt x1 x2 =
  match x1, x2 with
  | V(id1), V(id2) ->  id1 = id2
  | T(x1, uid1, arg1), T(x2, uid2, arg2) ->
    arg1 = arg2 && cong x1 x2 && uid1 < uid2
  | _ -> raise (Global.NotImplemented "Idnt.lt")

let is_top = function
  | V(_) -> true
  | C(_) -> assert false
  | T(_, _, _) -> false
  | N(_) -> true

let rec is_pos x =
  match x with
  | V(_) -> true
  | C(_) -> assert false
  | T(x', _, _) -> is_neg x'
  | N(_) -> true
and is_neg x =
  match x with
  | V(_) -> false
  | C(_) -> assert false
  | T(x', _, _) -> is_pos x'
  | N(_) -> false

let is_coeff = function
  | C(_) -> true
  | V(_) | T(_, _, _) | N(_) -> false

let rec base = function
  | V(id) | C(id) -> id
  | T(x, _, _) -> base x
  | N(n) -> string_of_int n

let string_of = Printer.string_of pr

(** {6 Operators} *)

let rename vmap x = List.assoc_default x x vmap

let rec rename_base f = function
  | V(id) -> V(f id)
  | C(id) -> C(f id)
  | T(x, uid, arg) -> T(rename_base f x, uid, arg)
  | N(n) -> N(int_of_string (f (string_of_int n)))

let rec reset_uid = function
  | V(id) -> V(id)
  | C(id) -> C(id)
  | T(x, uid, arg) -> T(reset_uid x, 0(*@todo*), arg)
  | N(n) -> N(n)

let ret_args f uid arity =
  T(f, uid, arity), List.init arity (fun i -> T(f, uid, i))

let ret_args_cls f uid arity =
  let cls_base = make ((string_of f) ^ "@") in
  T(f, uid, arity),
  List.init arity (fun i -> T(f, uid, i)),
  List.init arity (fun i -> T(cls_base, uid, i))


(** {6 Serialization/deserialization} *)

let vheader = "v"
let cheader = "c"
let nheader = "n"
let separator = "_sep_"

let rec serialize x =
  let chk_string_of x =
    let str = string_of x in
    try String.find str separator; assert false
    with Not_found -> str
  in
  match x with
  | V(_) -> vheader ^ separator ^ chk_string_of x
  | C(_) -> cheader ^ separator ^ chk_string_of x
  | N(_) -> nheader ^ separator ^ chk_string_of x
  | T(x, uid, arg) ->
    serialize x ^ separator ^ String.of_int uid ^ separator ^ String.of_int arg

let deserialize s =
  let int_of_string str =
    try int_of_string str
    with Failure "int_of_string" ->
      Logger.printf
        "\"%a\" cannot be interpreted as an integer@,"
        String.pr str;
      Logger.printf
        "exception in Idnt.deserialize: %a@,"
        String.pr s;
      raise Not_found
  in
  let rec aux x ss =
    match ss with
    | [] -> x
    | s1 :: s2 :: ss' -> aux (T(x, int_of_string s1, int_of_string s2)) ss'
    | _ ->
      Logger.printf "exception in Idnt.deserialize: %a@," String.pr s;
      raise Not_found
  in
  match String.nsplit s separator with
  | h :: s' :: ss ->
    if String.starts_with h vheader then aux (V(s')) ss
    else if String.starts_with h cheader then aux (C(s')) ss
    else if String.starts_with h nheader then aux (N(int_of_string s')) ss
    else begin
      Logger.printf "exception in Idnt.deserialize: %a@," String.pr s;
      raise Not_found
    end
  | _ ->
    Logger.printf "exception in Idnt.deserialize: %a@," String.pr s;
    raise Not_found
