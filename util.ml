exception Fatal of string
exception Unsupported of string
exception TimeOut
exception Killed

let fatal s = raise (Fatal s)
let unsupported s = raise (Unsupported s)
let timeout () = raise TimeOut
let killed () = raise Killed

let warning s = Format.eprintf "WARNING: %s@\n%!" s

let (!!) f = f ()
let (-|) f g x = f (g x)
let (|-) f g x = g (f x)
let (|@>) x f = f x; x
let (|@-) f g x = f x |@> g
let (|*>) x f = x
let (|*@>) x f = x
let (|@*>) x f = x
let (|@) x b f = if b then f x; x
let (|@!) x b f = if !b then f x; x
let (|@!!) x b f = if !!b then f x; x
let (|&) x b f = if b then f x else x
let (|&!) x b f = if !b then f x else x
let (|&!!) x b f = if !!b then f x else x
let (&>) f x = f x
(* usage: x |@flag&> print *)
(* usage: x |&flag&> trans *)
let (-$-) f x y = f y x
(* "f -$- x" = "fun y -> f y x" *)
(* "(-$-) (/) x" = "fun y -> y / x" *)
let (!?) x = Lazy.force x

let (=>) b1 b2 = not b1 || b2

let raise_assert_failure loc =
  let r = Str.regexp {|^File \"\(.*\)\", line \([0-9]+\), characters \([0-9]+\)-[0-9]+$|} in
  assert (Str.string_match r loc 0);
  let file = Str.matched_group 1 loc in
  let line = int_of_string @@ Str.matched_group 2 loc in
  let first = int_of_string @@ Str.matched_group 3 loc in
  raise (Assert_failure(file,line,first))

let assert_ ?__LOC__ f x =
  try
    assert (f x)
  with
  | Assert_failure loc as e ->
      match __LOC__ with
      | None -> raise e
      | Some loc -> raise_assert_failure loc
let assert_false ?__LOC__ _ =
  match __LOC__ with
  | None -> fatal "assert_false"
  | Some loc -> raise_assert_failure loc

let (@@@) = List.rev_append

let rec print_list_aux print punc last fm xs =
  match xs with
  | [] -> ()
  | [x] -> print fm x
  | x::xs ->
      Format.fprintf fm "@[%a@]" print x;
      Format.fprintf fm punc;
      Format.fprintf fm "%a" (print_list_aux print punc last) xs

let print_list print ?(first=false) ?(last=false) punc fm xs =
  if xs <> [] then
    let punc' = format_of_string punc in
    Format.fprintf fm "@[";
    if first then Format.fprintf fm punc';
    Format.fprintf fm "%a" (print_list_aux print punc' last) xs;
    if last then Format.fprintf fm punc';
    Format.fprintf fm "@]"

module IntSet =
  Set.Make(
    struct
      type t = int
      let compare = compare
    end)

module StringSet = Set.Make(String)

module Pair = struct
  let fst = fst
  let snd = snd
  let pair x y = x, y
  let copy x = x, x
  let pair_rev x y = y, x
  let swap (x,y) = y, x
  let make f g x = f x, g x
  let map f g (x,y) = f x, g y
  let map_same f (x,y) = f x, f y
  let map_fst f (x,y) = f x, y
  let map_snd f (x,y) = x, f y
  let curry f x y = f (x,y)
  let uncurry f (x,y) = f x y
  let fold = uncurry
  let unfold = make
  let add_left f x = f x, x
  let add_right f x = x, f x
  let to_list (x,y) = [x;y]
  let of_list xs =
    match xs with
    | [x;y] -> x,y
    | _ -> invalid_arg "Pair.of_list"
  let print f g ppf (x,y) = Format.fprintf ppf "@[(@[%a,@ %a@])@]" f x g y
  let eq eq1 eq2 (x,y) (x',y') = eq1 x x' && eq2 y y'
  let compare cmp1 cmp2 (x,y) (x',y') =
    let r = cmp1 x x' in
    if r <> 0 then
      r
    else
      cmp2 y y'
end

module Triple = struct
  let fst (x,y,z) = x
  let snd (x,y,z) = y
  let trd (x,y,z) = z
  let map f g h (x,y,z) = f x, g y, h z
  let map_fst f (x,y,z) = f x, y, z
  let map_snd f (x,y,z) = x, f y, z
  let map_trd f (x,y,z) = x, y, f z
  let curry f x y z = f (x,y,z)
  let uncurry f (x,y,z) = f x y z
  let to_list (x,y,z) = [x;y;z]
  let of_list xs =
    match xs with
    | [x;y;z] -> x,y,z
    | _ -> invalid_arg "Triple.of_list"
  let to_pair_r (x,y,z) = x, (y, z)
  let to_pair_l (x,y,z) = (x, y), z
  let of_pair_r (x,(y,z)) = x, y, z
  let of_pair_l ((x,y),z) = x, y, z
  let take12 (x,y,z) = x, y
  let take13 (x,y,z) = x, z
  let take23 (x,y,z) = y, z
  let print f g h ppf (x,y,w) = Format.fprintf ppf "@[(@[%a,@ %a,@ %a@])@]" f x g y h w
end

module Quadruple = struct
  let fst (x,y,z,w) = x
  let snd (x,y,z,w) = y
  let trd (x,y,z,w) = z
  let fth (x,y,z,w) = w
  let curry f x y z w = f (x,y,z,w)
  let uncurry f (x,y,z,w) = f x y z w
  let to_list (x,y,z,w) = [x;y;z;w]
  let of_list xs =
    match xs with
    | [x;y;z;w] -> x,y,z,w
    | _ -> invalid_arg "Quadruple.of_list"
  let to_pair_r (x,y,z,w) = x, (y, (z, w))
  let to_pair_m (x,y,z,w) = (x, y), (z, w)
  let to_pair_l (x,y,z,w) = ((x, y), z), w
  let to_13 (x,y,z,w) = x, (y, z, w)
  let to_22 (x,y,z,w) = (x, y), (z, w)
  let to_31 (x,y,z,w) = (x, y, z), w
end

module Fun = struct
  external id : 'a -> 'a = "%identity"
  let fst x y = x
  let snd x y = y
  let flip f x y = f y x
  let curry2 = Pair.curry
  let uncurry2 = Pair.uncurry
  let curry3 = Triple.curry
  let uncurry3 = Triple.uncurry
  let curry4 = Quadruple.curry
  let uncurry4 = Quadruple.uncurry
  let curry = curry2
  let uncurry = uncurry2
  let rec repeat f n x =
    if n <= 0
    then x
    else repeat f (n-1) (f x)
  let const x _ = x
  let const2 x _ _ = x
  let ignore2 _ _  = ()
  let ignore3 _ _ _ = ()
  let if_ cond f1 f2 x = if cond x then f1 x else f2 x
  let cond b f x = if b then f x else x
  let copy f x = f x x
end

module Option = struct
  include BatOption

  exception No_value

  let iter = may
  let apply = map

  let (>>=) = bind
  let return = some
  let lift = map
  let fmap = map

  let get x =
    match x with
    | None -> raise No_value
    | Some x -> x

  let make check x =
    if check x
    then Some x
    else None

  let some_if f x = if f x then Some x else None

  let to_list x =
    match x with
    | None -> []
    | Some x' -> [x']

  let of_list xs =
    match xs with
    | [] -> None
    | [x] -> Some x
    | _ -> invalid_arg "Option.of_list"

  let print pr fm x =
    match x with
    | None -> Format.fprintf fm "None"
    | Some x' -> Format.fprintf fm "Some %a" pr x'

  let try_with f h = try Some !!f with e when h e -> None
  let try_any f = try_with f (Fun.const true)

  let for_all f x =
    match x with
    | None -> true
    | Some y -> f y
  let exists f x =
    match x with
    | None -> false
    | Some y -> f y
end

module List = struct
  include BatList
  module L = Labels

  let singleton x = [x]
  let cons x xs = x::xs
  let snoc xs x = xs@[x]
  let hd_option xs =
    match xs with
    | [] -> None
    | x::_ -> Some x
  let hd_default xs x =
    match xs with
    | [] -> x
    | y::_ -> y
  let get xs =
    match xs with
    | [x] -> x
    | _ -> invalid_arg "List.get"

  let print pr fm xs = Format.fprintf fm "@[<hov 1>[%a]@]" (print_list pr ";@ ") xs

  let rec unfold_right f s =
    match f s with
    | None -> []
    | Some(x,s') -> x :: unfold_right f s'

  let rec unfold_left acc f s =
    match f s with
    | None -> acc
    | Some(x,s') -> unfold_left (x::acc) f s'
  let unfold_left f s = unfold_left [] f s

  let rec init n f i acc_rev =
    if i >= n
    then rev acc_rev
    else init n f (i+1) (f i :: acc_rev)
  let init n f = init n f 0 []

  let make n x = init n @@ Fun.const x

  (*** returns a list of integers [m;...;n-1] ***)
  let fromto m n = init (n-m) ((+) m)

  let rev_map_flatten f xs = fold_left (fun acc x -> f x @@@ acc) [] xs
  let rev_flatten_map = rev_map_flatten
  let flatten_map f xs = rev @@ rev_map_flatten f xs
  let flatten_mapi f xs = List.flatten @@ List.mapi f xs
  let rev_flatten xs = rev_map_flatten Fun.id xs
  let concat_map = flatten_map

  let rec tabulate n f rev_acc =
    if n < 0 then
      invalid_arg "List.tabulate"
    else if n = 0 then
      rev rev_acc
    else
      tabulate (n-1) f (f n::rev_acc)
  let tabulate n f = tabulate n f []

  let count f xs =
    fold_left (fun acc n -> if f n then acc+1 else acc) 0 xs

  let rec decomp_snoc = function
    | [] -> invalid_arg "List.decomp_snoc"
    | [x] -> [], x
    | x::xs -> Pair.map_fst (cons x) @@ decomp_snoc xs

  let rec decomp_snoc_option = function
    | [] -> None
    | [x] -> Some ([], x)
    | x::xs -> Option.map (Pair.map_fst (cons x)) @@ decomp_snoc_option xs

  let rec mapi2 f i xs ys =
    match xs,ys with
    | [],[] -> []
    | x::xs',y::ys' -> f i x y :: mapi2 f (i+1) xs' ys'
    | _ -> invalid_arg "List.mapi2"
  let mapi2 f xs ys = mapi2 f 0 xs ys

  let rec rev_map2 f acc xs ys =
    match xs,ys with
    | [],[] -> acc
    | x::xs',y::ys' -> rev_map2 f (f x y::acc) xs' ys'
    | _ -> invalid_arg "List.rev_map2"
  let rev_map2 f xs ys = rev_map2 f [] xs ys

  let rec map3 f xs ys zs =
    match xs,ys,zs with
    | [],[],[] -> []
    | x::xs',y::ys',z::zs' -> f x y z :: map3 f xs' ys' zs'
    | _ -> invalid_arg "List.map3"

  let rec rev_iter f xs =
    match xs with
    | [] -> ()
    | x::xs' -> rev_iter f xs'; f x

  let rec rev_filter_map acc f xs =
    match xs with
    | [] -> acc
    | x::xs' ->
        let acc' =
          match f x with
          | None -> acc
          | Some r -> r::acc
        in
        rev_filter_map acc' f xs'
  let rev_filter_map f xs = rev_filter_map [] f xs
  let filter_map2 f xs ys = rev_filter_map Fun.id @@ rev_map2 f xs ys
  let filter_mapi f xs = filter_map Fun.id @@ List.mapi f xs

  let filter_out f xs = filter (not -| f) xs
  let filteri f xs = filter_map Fun.id @@ List.mapi (fun i x -> if f i x then Some x else None) xs

  let rev_split xs = fold_left (fun (acc1,acc2) (x,y) -> x::acc1, y::acc2) ([],[]) xs
  let split_map f = rev_split -| rev_map f

  let split3 xs = fold_right (fun (x,y,z) (acc1,acc2,acc3) -> x::acc1, y::acc2, z::acc3) xs ([],[],[])

  let replace_nth xs i y = mapi (fun j x -> if j = i then y else x) xs
  let update = replace_nth
  let set = replace_nth

  let mem ?(eq=(=)) x xs = exists (eq x) xs
  let mem_on ?(eq=(=)) f x xs =
    let x' = f x in
    exists (eq x' -| f) xs

  let find_eq_on ?(eq=(=)) f x xs =
    let x' = f x in
    find (eq x' -| f) xs

  let assoc ?(eq=(=)) x xs =
    snd @@ find (eq x -| fst) xs

  let assoc_on ?(eq=(=)) f x xs =
    let x' = f x in
    snd @@ find_eq_on ~eq (f -| fst) x' xs

  let mem_assoc ?(eq=(=)) x xs =
    try
      ignore @@ assoc ~eq x xs;
      true
    with Not_found -> false

  let mem_assoc_on ?(eq=(=)) f x xs =
    try
      ignore @@ assoc_on ~eq f x xs;
      true
    with Not_found -> false

  let find_default d f xs =
    try
      find f xs
    with Not_found -> d

  let find_option f xs =
    try
      Some (find f xs)
    with Not_found -> None

  let rec find_map_option f xs =
    match xs with
    | [] -> None
    | x::xs' ->
        match f x with
        | None -> find_map_option f xs'
        | Some y -> Some y

  let rec find_map f xs =
    match find_map_option f xs with
    | None -> raise Not_found
    | Some x -> x

  let find_pos f xs =
    fst @@ findi f xs

  let assoc_default ?(eq=(=)) x k tbl =
    try
      assoc ~eq k tbl
    with Not_found -> x

  let assoc_option ?(eq=(=)) k tbl =
    try
      Some (assoc ~eq k tbl)
    with Not_found -> None

  let rec assoc_map ?(eq=(=)) k f tbl =
    match tbl with
    | [] -> raise Not_found
    | (k',x)::tbl' ->
        if eq k k'
        then x, (k', f x) :: tbl'
        else assoc_map ~eq k f tbl' |> Pair.map_snd @@ cons (k', x)

  let rec decomp_assoc ?(eq=(=)) k tbl =
    match tbl with
    | [] -> raise Not_found
    | (k',x)::tbl' ->
        if eq k k'
        then x, tbl'
        else decomp_assoc ~eq k tbl' |> Pair.map_snd @@ cons (k', x)

  let rec classify ?(eq=(=)) xs =
    let rec aux rev_acc xs =
      match xs with
      | [] -> List.rev rev_acc
      | x::xs' ->
          let xs1,xs2 = List.partition (eq x) xs' in
          aux ((x::xs1)::rev_acc) xs2
    in
    aux [] xs

  let rec is_prefix ?(eq=(=)) xs ys =
    match xs, ys with
    | [], _ -> true
    | _, [] -> false
    | br1::ce1', br2::ce2' -> eq br1 br2 && is_prefix ce1' ce2'

  let remove_lower is_lower xs =
    let rec aux acc_rev xs =
      match xs with
      | [] -> List.rev acc_rev
      | x::xs' ->
          let acc_rev' = if exists (is_lower x) acc_rev || exists (is_lower x) xs' then acc_rev else x::acc_rev in
          aux acc_rev' xs'
    in
    aux [] xs

  let assoc_all ?(eq=(=)) k tbl = filter_map (fun (k',x) -> if eq k k' then Some x else None) tbl

  let fold_trans_right tr dec cons env xs =
    let aux x (env,rs) =
      let env',r = tr env @@ dec x in
      env', cons r::rs
    in
    fold_right aux xs (env,[])

  let for_alli f xs = List.for_all (Fun.uncurry f) @@ List.mapi Pair.pair xs

  let eq ?(eq=(=)) xs ys = length xs = length ys && for_all2 eq xs ys

  let transpose xss =
    match xss with
    | [] -> []
    | xs::_ ->
        let m = List.length xss in
        let n = List.length xs in
        init n (fun i -> init m (fun j -> List.nth (nth xss j) i))

  let rec is_unique ?(eq=(=)) xs =
    match xs with
    | [] | [_] -> true
    | x::xs' -> List.for_all (not -| eq x) xs' && is_unique xs'

  let reduce_left = reduce
  let reduce_right f ts =
    match ts with
    | [] -> invalid_arg "Empty List"
    | _ ->
        let ts',t = decomp_snoc ts in
        List.fold_right f ts' t

  let to_string ?(delimiter=";") f xs =
    "[" ^ BatString.join delimiter (List.map f xs) ^ "]"

  let takedrop_while f xs =
    let rec go acc_rev xs =
      match xs with
      | [] -> List.rev acc_rev, []
      | x::_ when not (f x) -> List.rev acc_rev, xs
      | x::xs' -> go (x::acc_rev) xs'
    in
    go [] xs

  module Set = struct
    let diff ?(eq=(=)) l1 l2 = filter_out (mem ~eq -$- l2) l1
    let inter ?(eq=(=)) l1 l2 = filter (mem ~eq -$- l2) l1
    let subset ?(eq=(=)) l1 l2 = for_all (mem ~eq -$- l2) l1
    let supset ?(eq=(=)) l1 l2 = subset ~eq l2 l1
    let eq ?(eq=(=)) l1 l2 = subset ~eq l1 l2 && supset ~eq l1 l2
    let union ?(eq=(=)) l1 l2 = rev_append l1 @@ diff ~eq l2 l1
    let disjoint ?(eq=(=)) l1 l2 = inter ~eq l1 l2 = []
  end
end

module Focus = struct
  let fst (x,y) = (fun z -> z,y), x
  let snd (x,y) = (fun z -> x,z), y
  let (|-) f g x =
    let ctx1,y = f x in
    let ctx2,z = g y in
    ctx2 |- ctx1, z
  let (-|) f g x = (g |- f) x
end

let topological_sort ?(eq=(=)) edges =
  let rec loop edges roots xs rev_acc =
    match roots with
    | [] -> xs @@@ List.rev rev_acc
    | r::roots' ->
        let edges1,edges2 = List.partition (fst |- eq r) edges in
        let roots'' =
          let ys = List.map snd edges1 in
          List.filter (fun y -> not @@ List.exists (snd |- eq y) edges2) ys @ roots'
        in
        let xs' = List.filter_out (eq r) xs in
        let rev_acc' = r::rev_acc in
        loop edges2 roots'' xs' rev_acc'
  in
  let xs = List.unique ~eq @@ List.flatten_map Pair.to_list edges in
  let roots = List.filter_out (fun x -> List.exists (snd |- eq x) edges) xs in
  loop edges roots xs []

module Compare = struct
  let on ?(cmp=compare) f x y = cmp (f x) (f y)
  let eq_on ?(eq=(=)) f x y = eq (f x) (f y)
  let topological ?(eq=(=)) ?dom edges =
    let map =
      let dom' =
        match dom with
        | None -> List.unique ~eq @@ List.flatten_map Pair.to_list edges
        | Some dom' -> dom'
      in
      let no_edge = List.filter_out (fun x -> List.exists (fun (y,z) -> eq x y || eq x z) edges) dom' in
      edges
      |> topological_sort ~eq
      |> (@) no_edge
      |> List.mapi (fun i x -> x, i)
    in
    on (List.assoc ~eq -$- map)
end

module Array = BatArray

module Hashtbl = BatHashtbl

module Map = BatMap

module Char = BatChar

module String = struct
  include BatString

  let tl s =
    sub s 1 (length s - 1)

  let split_nth s n =
    sub s 0 n, sub s n (length s - n)

  let count_line s =
    fold_left (fun n c -> if c = '\n' then n+1 else n) 0 s

  let remove_char c s =
    replace_chars (fun c' -> if c = c' then "" else of_char c') s

  let of_sign c =
    match c with
    | '!' -> Some "bang"
    | '$' -> Some "dollar"
    | '%' -> Some "percent"
    | '&' -> Some "ampersand"
    | '*' -> Some "asterisk"
    | '+' -> Some "plus"
    | '-' -> Some "minus"
    | '.' -> Some "dot"
    | '/' -> Some "slash"
    | ':' -> Some "colon"
    | '<' -> Some "lessthan"
    | '=' -> Some "equal"
    | '>' -> Some "greaterthan"
    | '?' -> Some "question"
    | '@' -> Some "at"
    | '^' -> Some "caret"
    | '|' -> Some "bar"
    | '~' -> Some "tilde"
    | '\'' -> Some "prime"
    | _ -> None

  let sign_to_letters s =
    let map c =
      match of_sign c with
      | None -> make 1 c
      | Some s -> "_" ^ s ^ "_"
    in
    replace_chars map s

  let split_blanc s =
    let quots = ['\''; '\"'] in
    let rec parse quot acc cs =
      match quot, acc, cs with
      | None,   [], [] -> []
      | None,   _,  [] -> [of_list acc]
      | None,   _,  c::cs' when List.mem c quots -> parse (Some c) acc cs'
      | None,   [], c::cs' when Char.is_whitespace c -> parse None acc cs'
      | None,   _,  c::cs' when Char.is_whitespace c -> of_list acc :: parse None [] cs'
      | None,   _,  c::cs' -> parse None (acc@[c]) cs'
      | Some q, _,  [] -> invalid_arg "String.split_blanc"
      | Some q, _,  c::cs' when List.mem c quots ->
          if c = q then
            parse None acc cs'
          else
            parse quot (acc@[c]) cs'
      | Some q, _,  c::cs' -> parse quot (acc@[c]) cs'
    in
    parse None [] @@ to_list s

  let escape_for_sh s =
    let s' = Format.sprintf "%S" s in
    if List.exists Char.is_whitespace @@ to_list s then
      s'
    else if contains s '\'' then
      s'
    else if String.length s' > String.length s + 2 then
      s'
    else
      s
end

module Math = struct
  let rec gcd m n =
    if m < n then gcd n m
    else if n = 0 then m
    else gcd n (m mod n)

  let pi = 2. *. acos 0.
end

module Random = struct
  include Random

  let gaussian d =
    let x = float 1. in
    let y = float 1. in
    d *. sqrt (-2. *. log x) *. cos (2. *. Math.pi *. y)

  let string ?(cs="0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz") n =
    let len = String.length cs in
    String.init n (fun _ -> cs.[Random.int len])
end

module Format = struct
  include Format
  let dummy_formatter = make_formatter Fun.ignore3 ignore
end

module Filename = struct
  include Filename

  let chop_extension_if_any filename =
    try
      chop_extension filename
    with Invalid_argument _ -> filename

  let change_extension filename ext =
    chop_extension_if_any filename ^ "." ^ ext
end

module Exception = struct
  let not_raise f x =
    try
      ignore @@ f x; true
    with _ -> false
  let finally = BatPervasives.finally
end

module IO = struct
  module CPS = struct
    let open_in file k =
      let cin = open_in file in
      Exception.finally
        (fun () -> close_in cin)
        k cin

    let open_out file k =
      let cout = open_out file in
      Exception.finally
        (fun () -> close_out cout)
        k cout
  end

  let input_all = BatPervasives.input_all
  let input_file = BatPervasives.input_file
  let output_file = BatPervasives.output_file
  let copy_file ~src ~dest =
    let text = input_file src in
    output_file ~filename:dest ~text
  let empty_file file = output_file file ""
end


module Ref = struct
  let map f x =
    x := f !x

  let set = (:=)
  let deref = (!)

  let tmp_set x v f =
    let prev = !x in
    x := v;
    Exception.finally (fun () -> x := prev) f ()
end

module Counter : sig
  type t
  val create : unit -> t
  val peep : t -> int
  val gen : t -> int
  val reset : t -> unit
  val stash : t -> unit
  val pop : t -> unit
end
  =
struct
  type t = int ref * int list ref

  let init = 0
  let create () = ref init, ref []
  let peep ((c,_)) = !c
  let gen ((c,_)) = incr c; !c
  let reset ((c,_)) = c := init

  let stash (c,s as cnt) = s := !c::!s; reset cnt
  let pop (c,s) = s := List.tl !s
end

module Combination = struct
  let rec take_each xxs =
    match xxs with
    | [] -> [[]]
    | xs::xxs' ->
        let cmb = take_each xxs' in
        List.flatten_map (fun x -> List.map (List.cons x) cmb) xs

  let product xs ys =
    List.flatten_map (fun p -> List.map (fun p' -> p',p) xs) ys
end

module Arg = struct
  include Arg
  let separator = '_'
  let align args =
    let aux i (s,f,desc) =
      if s = "" then
        let nr = if i <> 0 then "\n  " else "" in
        let s' =
          desc
          |> String.trim
          |> String.map (fun c -> if c = separator then ' ' else c)
          |> Format.sprintf "%s(*** %s ***)" nr
        in
        s', f, " "
      else
        let aux c =
          if c = '\n' then
            let rec len i =
              if desc.[i] = ' ' then
                1 + len (i+1)
              else 3
            in
            "\n" ^ String.make (String.length s + len 0) ' '
          else
            String.of_char c
        in
        s, f, String.replace_chars aux desc
    in
    args
    |> List.map (fun (s,f,desc) -> if s = "" then s,f," "^desc else s,f,desc)
    |> align
    |> List.mapi aux

  let filter_out_desc args =
    List.filter_out (fun (s,_,_) -> s.[0] = '\n') args
end

module Marshal = struct
  include BatMarshal

  let to_file ?(flag=[]) file x =
    IO.CPS.open_out file (fun cout -> Marshal.to_channel cout x flag)

  let from_file file default =
    if Sys.file_exists file then
      IO.CPS.open_in file Marshal.from_channel
    else
      default

  let from_file_exn file =
    IO.CPS.open_in file Marshal.from_channel
end


module Unix = struct
  include Unix

  let parallel ?(wait = fun _ -> wait()) limit cmds =
    let rec loop running waiting =
      let debug = false in
      if debug then Format.printf "|running|: %d@." (List.length running);
      if debug then Format.printf "limit: %d@." limit;
      if debug then Format.printf "|waiting|: %d@.@." (List.length waiting);
      if limit = List.length running || waiting = [] then
        let pid,status = wait running in
        let i = List.assoc pid running in
        if debug then Format.printf "DONE #%d (pid: %d)@." i pid;
        let running' = List.filter_out (fst |- (=) pid) running in
        (if running' <> [] || waiting <> [] then loop running' waiting)
      else
        match waiting with
        | [] -> invalid_arg "Util.Unix.parallel"
        | (i, cmd)::waiting' ->
            let pid = create_process "sh" [|"sh"; "-c"; cmd|] stdin stdout stderr in
            if debug then Format.printf "Run #%d by process %d@." i pid;
            let running' = (pid,i)::running in
            loop running' waiting'
    in
    cmds
    |> List.mapi Pair.pair
    |> loop []

  module CPS = struct
    let open_process ?(check=ignore) cmd k =
      let cin,cout = open_process cmd in
      let r = k cin cout in
      let st = close_process (cin, cout) in
      check st;
      r

    let open_process_in ?(check=ignore) cmd k =
      let cin = open_process_in cmd in
      let r = k cin in
      let st = close_process_in cin in
      check st;
      r
  end
end


module Time = struct
  let get () =
    let open Unix in
    let tm = times() in
    tm.tms_utime +. tm.tms_cutime

  let add tmp t = t := !t +. !!get -. tmp

  let measure f =
    let tmp = !!get in
    let r = !!f in
    !!get -. tmp, r

  let measure_and_add t f x =
    let tmp = !!get in
    let fend () = t := !t +. (!!get -. tmp) in
    Exception.finally fend f x

  let string_of_tm {Unix.tm_sec;tm_min;tm_hour;tm_mday;tm_mon;tm_year;tm_wday;tm_yday;tm_isdst} =
    Format.sprintf "%04d/%02d/%02d %02d:%02d:%02d" (tm_year+1900) (tm_mon+1) tm_mday tm_hour tm_min tm_sec

  let string_of_tm_simple {Unix.tm_sec;tm_min;tm_hour;tm_mday;tm_mon;tm_year;tm_wday;tm_yday;tm_isdst} =
    Format.sprintf "%04d%02d%02d%02d%02d%02d" (tm_year+1900) (tm_mon+1) tm_mday tm_hour tm_min tm_sec

  let string_of_current_local () =
    string_of_tm @@ Unix.localtime !!Unix.time

  let print fm t =
    Format.pp_print_string fm @@ string_of_tm @@ Unix.localtime t

  let print_simple fm t =
    Format.pp_print_string fm @@ string_of_tm_simple @@ Unix.localtime t
end


module CommandLine = struct
  let confirm ?(default=true) ?(yes=false) s =
    let yn = if default then "[Y/n]" else "[y/N]" in
    let rec aux () =
      Format.printf "%s %s @?" s yn;
      if yes then
        (Format.printf "y@?"; true)
      else
        match read_line() with
        | "" -> default
        | "y" -> true
        | "n" -> false
        | _ -> aux ()
    in
    aux ()
end

module Cursor = struct
  let up fm n = Format.fprintf fm "\027[%dA" n
  let down fm n = Format.fprintf fm "\027[%dB" n
  let left fm n = Format.fprintf fm "\027[%dC" n
  let right fm n = Format.fprintf fm "\027[%dD" n
  let down_begin fm n = Format.fprintf fm "\027[%dE" n
  let up_begin fm n = Format.fprintf fm "\027[%dF" n
  let show fm = Format.fprintf fm "\027[?25h"
  let hide fm = Format.fprintf fm "\027[?25l"
end


module JSON = struct
  include Yojson.Basic

  let load file of_json =
    IO.CPS.open_in file @@
      (IO.input_all
       |- from_string
       |- of_json)

  let save ?(pretty=false) file to_json data =
    let to_s json = if pretty then pretty_to_string json else to_string json in
    IO.CPS.open_out file @@
      (output_string -$- (to_s @@ to_json data))
end

(* This function uses '\b' *)
let print_begin_end ?(fm=Format.std_formatter) =
  let pre fm = Format.fprintf fm "%s" "BEGIN" in
  let post fm r = Format.fprintf fm "%s" "END" in
  fun ?(pre=pre) ?(post=post) f ->
    Format.fprintf fm "@[<v 2>%t@ " pre;
    f ()
    |@> Format.fprintf fm "@]\b\b%a@\n" post


let rec fixed_point ?(eq=(=)) ?(max= -1) f init =
  let x = f init in
  if eq x init || max = 0
  then x
  else fixed_point ~eq ~max:(max-1) f x


let rec transitive_closure ?(eq=(=)) edges =
  let eq' = Pair.eq eq eq in
  let cons (x,y) es =
    if List.mem ~eq:eq' (x,y) es then
      es
    else
      (x,y)::es
  in
  let f edges' =
    let aux acc (x,y) =
      List.fold_left (fun acc' (z,w) -> if eq y z then cons (x,w) acc' else acc') acc acc
    in
    List.fold_left aux edges' edges'
  in
  fixed_point ~eq:(List.Set.eq ~eq:eq') f edges
