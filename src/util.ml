exception Unsupported of string
exception TimeOut
exception Killed
exception Found

(* Exceptions *)
let failwith fmt = Format.kasprintf failwith fmt
let invalid_arg fmt = Format.kasprintf invalid_arg fmt
let unsupported fmt = Format.kasprintf (fun s -> raise (Unsupported s)) fmt
let timeout () = raise TimeOut
let killed () = raise Killed

let warning_history = ref []
let warning fmt =
  let cont s =
    if not (List.mem s !warning_history) then begin
      warning_history := s :: !warning_history;
      Format.eprintf "%s@\n%!" s
    end
  in
  Format.kasprintf cont ("WARNING: "^^fmt)

let (!!) f = f ()
let (-|) f g x = f (g x)
let (|-) f g x = g (f x)
let (|--) f g x y = g (f x y)
let (--|) f g x y = f (g x y)
let (|@>) x f = f x; x
let (|@-) f g x = f x |@> g
let (|*>) x _f = x
let (|*@>) x _f = x
let (|@*>) x _f = x
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
let (&&&) f g x = f x && g x
let (|||) f g x = f x || g x
let (!?) x = Lazy.force x
let (let@) f k = f k
let (=>) b1 b2 = not b1 || b2
let (@@@) = List.rev_append

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
  | Assert_failure _ as e ->
      match __LOC__ with
      | None -> raise e
      | Some loc -> raise_assert_failure loc
let assert_false ?__LOC__ _ =
  match __LOC__ with
  | None -> failwith "assert_false"
  | Some loc -> raise_assert_failure loc

let rec print_list_aux_with_flag ?(first=true) print punc fm xs =
  match xs with
  | [] -> ()
  | [x] -> print ~first ~last:true fm x
  | x::xs ->
      Format.fprintf fm "@[%a@]" (print ~first ~last:false) x;
      Format.fprintf fm punc;
      Format.fprintf fm "%a" (print_list_aux_with_flag print punc ~first:false) xs

let print_list_aux print punc fm xs =
  let print ~first ~last fm x = print fm x in
  print_list_aux_with_flag print punc fm xs
  [@@ocaml.warning "-27"]

let print_list_with_flag print ?(box=ignore) ?(first=false) ?(last=false) ?limit punc fm xs =
  if xs <> [] then
    let exceed = match limit with None -> false | Some limit -> limit >= 0 && List.length xs > limit in
    let xs = if exceed then BatList.take (Option.get limit) xs else xs in
    let punc' = format_of_string punc in
    Format.fprintf fm "@[";
    box fm;
    if first then Format.fprintf fm punc';
    Format.fprintf fm "%a" (print_list_aux_with_flag print punc') xs;
    if exceed && limit > Some 0 then Format.fprintf fm punc';
    if exceed then Format.fprintf fm "...";
    if last then Format.fprintf fm punc';
    Format.fprintf fm "@]"

let print_list print ?(box=ignore) ?(first=false) ?(last=false) ?limit punc fm xs =
  let print ~first ~last fm x = print fm x in
  print_list_with_flag print ~box ~first ~last ?limit punc fm xs
  [@@ocaml.warning "-27"]

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
    | _ -> invalid_arg "%s" __FUNCTION__
  let print f g ppf (x,y) = Format.fprintf ppf "@[(@[%a,@ %a@])@]" f x g y
  let eq eq1 eq2 (x,y) (x',y') = eq1 x x' && eq2 y y'
  let compare cmp1 cmp2 (x,y) (x',y') =
    let r = cmp1 x x' in
    if r <> 0 then
      r
    else
      cmp2 y y'
  let iter f g (x,y) = f x; g y
end

module Triple = struct
  let triple x y z = x, y, z
  let fst (x,_,_) = x
  let snd (_,y,_) = y
  let trd (_,_,z) = z
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
    | _ -> invalid_arg "%s" __FUNCTION__
  let to_pair_r (x,y,z) = x, (y, z)
  let to_pair_l (x,y,z) = (x, y), z
  let of_pair_r (x,(y,z)) = x, y, z
  let of_pair_l ((x,y),z) = x, y, z
  let take12 (x,y,_) = x, y
  let take13 (x,_,z) = x, z
  let take23 (_,y,z) = y, z
  let print f g h ppf (x,y,w) = Format.fprintf ppf "@[(@[%a,@ %a,@ %a@])@]" f x g y h w
end

module Quadruple = struct
  let fst (x,_,_,_) = x
  let snd (_,y,_,_) = y
  let trd (_,_,z,_) = z
  let fth (_,_,_,w) = w
  let curry f x y z w = f (x,y,z,w)
  let uncurry f (x,y,z,w) = f x y z w
  let to_list (x,y,z,w) = [x;y;z;w]
  let of_list xs =
    match xs with
    | [x;y;z;w] -> x,y,z,w
    | _ -> invalid_arg "%s" __FUNCTION__
  let to_pair_r (x,y,z,w) = x, (y, (z, w))
  let to_pair_m (x,y,z,w) = (x, y), (z, w)
  let to_pair_l (x,y,z,w) = ((x, y), z), w
  let to_13 (x,y,z,w) = x, (y, z, w)
  let to_22 (x,y,z,w) = (x, y), (z, w)
  let to_31 (x,y,z,w) = (x, y, z), w
end

module Fun = struct
  external id : 'a -> 'a = "%identity"
  let fst x _ = x
  let snd _ y = y
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
  include Option
  include BatOption

  exception No_value

  let iter = may
  let apply = map

  let (let*) = bind
  let (let**) x f =
    match x with
    | None -> None
    | Some y -> try f y with _ -> None
  let (>>=) = bind
  let (>=>) f g = fun x -> f x >>= g
  let return = some
  let lift = map
  let fmap = map
  let guard b = if b then Some () else None

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
  let try_with_any f = try_with f (Fun.const true)
  let try_with_not_found f x = try Some (f x) with Not_found -> None

  let for_all f x =
    match x with
    | None -> true
    | Some y -> f y
  let exists f x =
    match x with
    | None -> false
    | Some y -> f y

  let merge (++) x y =
    match x, y with
    | None, None -> None
    | Some x, None -> Some x
    | None, Some y -> Some y
    | Some x, Some y -> Some (x ++ y)
  let join = merge
end

module List = struct
  include BatList

  let singleton x = [x]
  let cons x xs = x::xs
  let snoc xs x = xs@[x]
  let hd_opt xs =
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

  let is_singleton xs = length xs = 1

  let print ?limit pr fm xs = Format.fprintf fm "@[<hov 1>[%a]@]" (print_list ?limit pr ";@ ") xs

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
  let flatten_mapi f xs = flatten @@ mapi f xs
  let rev_flatten xs = rev_map_flatten Fun.id xs
  let concat_map = flatten_map
  let map_append f xs ys = fold_right (fun x acc -> f x :: acc) xs ys
  let rev_map_append f xs ys = fold_left (fun acc x -> f x :: acc) ys xs

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

  let decomp_cons = function
    | [] -> invalid_arg "List.decomp_cons"
    | x::xs -> x, xs

  let rec decomp_snoc = function
    | [] -> invalid_arg "List.decomp_snoc"
    | [x] -> [], x
    | x::xs -> Pair.map_fst (cons x) @@ decomp_snoc xs

  let rec decomp_snoc_opt = function
    | [] -> None
    | [x] -> Some ([], x)
    | x::xs -> Option.map (Pair.map_fst (cons x)) @@ decomp_snoc_opt xs

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
  let filter_mapi f xs = filter_map Fun.id @@ mapi f xs

  let filter_out f xs = filter (not -| f) xs
  let filteri f xs = filter_map Fun.id @@ mapi (fun i x -> if f i x then Some x else None) xs

  let rev_split xs = fold_left (fun (acc1,acc2) (x,y) -> x::acc1, y::acc2) ([],[]) xs
  let split_map f = rev_split -| rev_map f

  let split3 xs = fold_right (fun (x,y,z) (acc1,acc2,acc3) -> x::acc1, y::acc2, z::acc3) xs ([],[],[])

  let replace_nth xs i y = mapi (fun j x -> if j = i then y else x) xs
  let set = replace_nth

  let add_index xs = mapi Pair.pair xs

  let mem ?(eq=(=)) x xs = exists (eq x) xs
  let mem_on ?(eq=(=)) f x xs =
    let x' = f x in
    exists (eq x' -| f) xs

  let rec find_mapi f i = function
    | [] -> raise Not_found
    | x::xs' ->
        match f i x with
        | None -> find_mapi f (i+1) xs'
        | Some r -> r
  let find_mapi f xs = find_mapi f 0 xs

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

  let rec find_map_opt f xs =
    match xs with
    | [] -> None
    | x::xs' ->
        match f x with
        | None -> find_map_opt f xs'
        | Some y -> Some y

  let find_map f xs =
    match find_map_opt f xs with
    | None -> raise Not_found
    | Some x -> x

  let find_map_default f x xs =
    match find_map_opt f xs with
    | None -> x
    | Some x -> x

  let find_pos f xs =
    fst @@ findi f xs

  let rec find_decomp f xs =
    match xs with
    | [] -> raise Not_found
    | x::xs' ->
        if f x then
          x, xs'
        else
          let y,xs'' = find_decomp f xs' in
          y, x::xs''

  let find_decomp_opt f xs =
    try
      Some (find_decomp f xs)
    with Not_found -> None

  let assoc_default ?(eq=(=)) x k tbl =
    try
      assoc ~eq k tbl
    with Not_found -> x

  let assoc_opt ?(eq=(=)) k tbl =
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

  let subst ?(eq=(=)) map x = assoc_default ~eq x x map

  let classify ?(eq=(=)) xs =
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

  let eq ?(eq=(=)) xs ys = compare_lengths xs ys = 0 && for_all2 eq xs ys

  let transpose xss =
    match xss with
    | [] -> []
    | xs::_ ->
        let m = List.length xss in
        let n = List.length xs in
        init n (fun i -> init m (fun j -> List.nth (nth xss j) i))

  let cons_unique ?(eq=(=)) x xs =
    if mem ~eq x xs then
      xs
    else
      x::xs

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

  let rec is_unique ?(eq=(=)) xs =
    match xs with
    | [] -> true
    | [_] -> true
    | x::xs' -> List.for_all (not -| eq x) xs' && is_unique ~eq xs'

  let fold_right_map f xs acc =
    let aux x (acc,xs) =
      let acc,x' = f x acc in
      acc, x'::xs
    in
    fold_right aux xs (acc,[])

  let rec decomp_common_prefix ?(eq=(=)) xs ys =
    match xs, ys with
    | x::xs, y::ys when eq x y ->
        let prefix,xs',ys' = decomp_common_prefix xs ys in
        x::prefix, xs', ys'
    | _ -> [], xs, ys

  (* for OCaml <4.12.0 *)
  let rec equal eq l1 l2 =
    match l1, l2 with
    | [], [] -> true
    | [], _::_ | _::_, [] -> false
    | a1::l1, a2::l2 -> eq a1 a2 && equal eq l1 l2

  module Set = struct
    let diff ?(eq=(=)) l1 l2 = filter_out (mem ~eq -$- l2) l1
    let inter ?(eq=(=)) l1 l2 = filter (mem ~eq -$- l2) l1
    let subset ?(eq=(=)) l1 l2 = for_all (mem ~eq -$- l2) l1
    let supset ?(eq=(=)) l1 l2 = subset ~eq l2 l1
    let eq ?(eq=(=)) l1 l2 = subset ~eq l1 l2 && supset ~eq l1 l2
    let union ?(eq=(=)) l1 l2 = rev_append l1 @@ diff ~eq l2 l1
    let disjoint ?(eq=(=)) l1 l2 = inter ~eq l1 l2 = []
    let (=) = eq
    let (<=) = subset
    let (>=) = supset
    let (+) = union
    let (-) = diff
    let (&&) = inter
  end

  module type EqType = sig
    type 'a t
    val eq : 'a t -> 'a t -> bool
  end

  module Make(X : EqType) = struct
    let unique xs = unique ~eq:X.eq xs
    let mem x xs = mem ~eq:X.eq x xs
    let mem_on f x xs = mem_on ~eq:X.eq f x xs
    let find_eq_on f x xs = find_eq_on ~eq:X.eq f x xs
    let assoc x map = assoc ~eq:X.eq x map
    let mem_assoc x map = mem_assoc ~eq:X.eq x map
    let assoc_default x y map = assoc_default ~eq:X.eq x y map
    let assoc_opt x map = assoc_opt ~eq:X.eq x map
    let assoc_map x f map = assoc_map ~eq:X.eq x f map
    let decomp_assoc x map = decomp_assoc ~eq:X.eq x map
    let classify xs = classify ~eq:X.eq xs
    let is_prefix xs ys = is_prefix ~eq:X.eq xs ys
    let assoc_all x xs = assoc_all ~eq:X.eq x xs
    let cons_unique x xs = cons_unique ~eq:X.eq x xs
    let is_unique xs = is_unique ~eq:X.eq xs
    let subst map x = subst ~eq:X.eq map x
    module Set = struct
      let diff xs ys = Set.diff ~eq:X.eq xs ys
      let inter xs ys = Set.inter ~eq:X.eq xs ys
      let subset xs ys = Set.subset ~eq:X.eq xs ys
      let supset xs ys = Set.supset ~eq:X.eq xs ys
      let union xs ys = Set.union ~eq:X.eq xs ys
      let disjoint xs ys = Set.disjoint ~eq:X.eq xs ys
      let eq xs ys = Set.eq ~eq:X.eq xs ys
      let (=) = eq
      let (<=) = subset
      let (>=) = supset
      let (+) = union
      let (-) = diff
      let (&&) = inter
    end
    let eq xs ys = eq ~eq:X.eq xs ys
  end

  module L = struct
    let filter_out ~f xs = filter_out f xs
    let flatten_map = concat_map
    let fold_right_map ~init ~f xs = fold_right_map f xs init
    let fold_left_map ~init ~f xs = fold_left_map f init xs
    let find_map ~f xs = find_map f xs
    let find_map_opt ~f xs = find_map_opt f xs
    include Labels
  end
end

module Focus = struct
  let apply fcs_arg f fcs_ret x =
    let ctx_arg,y = fcs_arg x in
    let ctx_ret,r = fcs_ret (f y) in
    ctx_ret (ctx_arg r)
  let id x = Fun.id, x
  let fst (x,y) = (fun z -> z,y), x
  let snd (x,y) = (fun z -> x,z), y
  let (|-) f g x =
    let ctx1,y = f x in
    let ctx2,z = g y in
    ctx2 |- ctx1, z
  let (-|) f g x = (g |- f) x
end

module Exception = struct
  let not_raise ?exn f x =
    try
      ignore @@ f x; true
    with e when exn = None || Some e = exn -> false
  let does_raise ?exn f x = not (not_raise ?exn f x)
  let finally = BatPervasives.finally
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

module Fmap = struct
  let const = Fun.const
  let id = Fun.id
  let __ = id
  let option = Option.map
  let list = List.map
  let list2 = List.map2
  let fst = Pair.map_fst
  let snd = Pair.map_snd
  let fst3 = Triple.map_fst
  let snd3 = Triple.map_snd
  let trd = Triple.map_trd
  let pair = Pair.map
  let triple = Triple.map
  let pair_curry f g x y = f x, g y
  let ( * ) = pair
  let string = String.map
  let if_ = Fun.if_
end

let topological_sort ?(eq=(=)) edges =
  let rec loop edges roots xs rev_acc =
    match roots with
    | [] -> xs @@@ List.rev rev_acc
    | r::roots' ->
        let edges1,edges2 = List.partition (fst |- eq r) edges in
        let roots'' =
          let ys = List.map snd edges1 in
          List.filter_out (fun y -> List.exists (snd |- eq y) edges2) ys @ roots'
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
  let dict cmp1 x1 x2 cmp2 y1 y2 =
    let r = cmp1 x1 x2 in
    if r <> 0 then r
    else cmp2 y1 y2
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

module Eq = struct
  let on = Compare.eq_on
  let pair = Pair.eq
  let list eq x y = List.eq ~eq x y
  let ( * ) = pair
  let option = Option.eq
end

module Array = BatArray

module Hashtbl = BatHashtbl

module Map = BatMap

module Char = struct
  include BatChar
end

module String = struct
  include BatString

  let tl s =
    sub s 1 (length s - 1)

  let last s =
    s.[length s-1]

  let split_nth s n =
    sub s 0 n, sub s n (length s - n)

  let count_line s =
    fold_left (fun n c -> if c = '\n' then n+1 else n) 0 s

  let remove_char c s =
    filter ((<>) c) s

  let filter_out f s = filter (not -| f) s

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
    | '[' -> Some "lbracket"
    | ']' -> Some "rbracket"
    | '(' -> Some "lparen"
    | ')' -> Some "rparen"
    | ' ' -> Some "space"
    | _ -> None

  let is_sign = Option.is_some -| of_sign

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
      | Some _, _,  [] -> invalid_arg "String.split_blanc"
      | Some q, _,  c::cs' when List.mem c quots ->
          if c = q then
            parse None acc cs'
          else
            parse quot (acc@[c]) cs'
      | Some _, _,  c::cs' -> parse quot (acc@[c]) cs'
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

  let mem c s = index_opt s c <> None

  let remove_prefix_aux ~prefix s =
    match split s ~by:prefix with
    | "", s2 -> Some s2
    | _ -> None
    | exception Not_found -> None
  let remove_prefix ~prefix s =
    match remove_prefix_aux ~prefix s with
    | None -> invalid_arg "%s" __FUNCTION__
    | Some r -> r
  let remove_prefix_if_any ~prefix s =
    match remove_prefix_aux ~prefix s with
    | None -> s
    | Some r -> r

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
  let iprintf f = ifprintf Format.std_formatter f
end

module Filename = struct
  include Filename

  let decomp_extension filename =
    match String.rsplit filename ~by:"." with
    | exception Not_found -> None
    | ss -> Some ss

  let chop_extension_if_any filename =
    try
      chop_extension filename
    with Invalid_argument _ -> filename

  let change_extension filename ext =
    chop_extension_if_any filename ^ "." ^ ext
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
  let empty_file filename = output_file ~filename ~text:""
end


class counter = object (self)
  val init = 0
  val mutable counter = 0
  val mutable stash = []

  method peep = counter
  method gen = counter <- counter+1; counter
  method reset = counter <- init

  method stash = stash <- counter::stash; self#reset
  method pop = stash <- List.tl stash
end

module Combination = struct
  let rec take_each xxs =
    match xxs with
    | [] -> [[]]
    | xs::xxs' ->
        let cmb = take_each xxs' in
        List.concat_map (fun x -> List.map (List.cons x) cmb) xs

  let product xs ys =
    List.flatten_map (fun p -> List.map (fun p' -> p',p) xs) ys
end

module Nondet = struct
  let bind xs f = List.concat_map f xs
  let (>>=) = bind
  let (let*) = bind
  let return x = [x]
end

module Arg = struct
  include Arg
  let align args =
    args
    |> List.map (fun (s,f,desc) -> if s = "" then s,f," "^desc else s,f,desc)
    |> align
    |> List.mapi (fun i (s,f,desc) ->
           if s = "" then
             let nr = if i <> 0 then "\n  " else "" in
             let s' =
               desc
               |> String.trim
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
             s, f, String.replace_chars aux desc)
end

module Sys = struct
  include Sys
  let runtime_parameters_list () =
    !!runtime_parameters
    |> String.split_on_char ','
    |> List.remove_all -$- ""
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

  let size ?(flag=[]) x =
     String.length (to_string x flag)
end


module Unix = struct
  include Unix

  let parallel ?(wait = fun _ -> wait()) limit cmds =
    let rec loop running waiting =
      let fm = if false then Format.std_formatter else Format.dummy_formatter in
      Format.fprintf fm "|running|: %d@." (List.length running);
      Format.fprintf fm "limit: %d@." limit;
      Format.fprintf fm "|waiting|: %d@.@." (List.length waiting);
      if limit = List.length running || waiting = [] then
        let pid,_status = wait running in
        let i = List.assoc pid running in
        Format.fprintf fm "DONE #%d (pid: %d)@." i pid;
        let running' = List.filter_out (fst |- (=) pid) running in
        (if running' <> [] || waiting <> [] then loop running' waiting)
      else
        match waiting with
        | [] -> invalid_arg "Util.Unix.parallel"
        | (i, cmd)::waiting' ->
            let pid = create_process "sh" [|"sh"; "-c"; cmd|] stdin stdout stderr in
            Format.fprintf fm "Run #%d by process %d@." i pid;
            let running' = (pid,i)::running in
            loop running' waiting'
    in
    cmds
    |> List.mapi Pair.pair
    |> loop []

  module CPS = struct
    let open_process ?(check=ignore) cmd k =
      let ch = open_process cmd in
      let r = k ch in
      check (close_process ch);
      r

    let open_process_in ?(check=ignore) cmd k =
      let cin = open_process_in cmd in
      let r = k cin in
      let st = close_process_in cin in
      check st;
      r
  end

  let open_and_read_line cmd = CPS.open_process_in cmd input_line
  let open_and_read_all cmd = CPS.open_process_in cmd IO.input_all
end


module Lexing = struct
  include Lexing

  let print_position fm {pos_fname; pos_lnum; pos_cnum; pos_bol} =
  Format.fprintf fm "File %s, line %d, column %d" pos_fname pos_lnum (pos_cnum - pos_bol)
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

  let string_of_tm {Unix.tm_sec; tm_min; tm_hour; tm_mday; tm_mon; tm_year; tm_wday=_; tm_yday=_; tm_isdst=_} =
    Format.sprintf "%04d/%02d/%02d %02d:%02d:%02d" (tm_year+1900) (tm_mon+1) tm_mday tm_hour tm_min tm_sec

  let string_of_tm_simple {Unix.tm_sec; tm_min; tm_hour; tm_mday; tm_mon; tm_year; tm_wday=_; tm_yday=_; tm_isdst=_} =
    Format.sprintf "%04d%02d%02d%02d%02d%02d" (tm_year+1900) (tm_mon+1) tm_mday tm_hour tm_min tm_sec

  let string_of_current_local () =
    string_of_tm @@ Unix.localtime !!Unix.time

  let print fm t =
    Format.pp_print_string fm @@ string_of_tm @@ Unix.localtime t

  let print_simple fm t =
    Format.pp_print_string fm @@ string_of_tm_simple @@ Unix.localtime t
end


module CommandLine = struct
  let confirm ?(fm=Format.std_formatter) ?(default=true) ?(yes=false) s =
    let yn = if default then "[Y/n]" else "[y/N]" in
    let rec aux () =
      Format.fprintf fm "%s %s @?" s yn;
      if yes then
        (Format.fprintf fm "y@?"; true)
      else
        match read_line() with
        | "" -> default
        | "y" -> true
        | "n" -> false
        | _ -> aux ()
    in
    aux ()

  let rec read_int ?(fm=Format.std_formatter) ?(check=fun _ -> true) msg =
    Format.fprintf fm "%s: @?" msg;
    match read_int_opt() with
    | Some n when check n -> n
    | _ -> read_int ~check msg
end

module Timer = struct
  let set_handler f = Sys.set_signal Sys.sigvtalrm (Sys.Signal_handle f)
  let get () = Unix.((getitimer ITIMER_VIRTUAL).it_value)
  let set ?(force=false) t =
    if not force && !!get > 0. then invalid_arg "Timer.set";
    ignore Unix.(setitimer ITIMER_VIRTUAL {it_interval=0.; it_value=t})
  let reset () = set ~force:true 0.
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

module LazyList = struct
  include BatLazyList

  let singleton x = cons x nil

  let is_singleton l =
    match next l with
    | Nil -> false
    | Cons(_,l') ->
        match next l' with
        | Nil -> true
        | Cons _ -> false

  let rec eager_to_list l =
    if Lazy.is_val l then
      match Lazy.force l with
      | Nil -> []
      | Cons(x,l') -> x :: eager_to_list l'
    else
      []

  let rec of_lazy_list l =
    match l with
    | [] -> lazy Nil
    | x::l' -> lazy (Cons(Lazy.force x, of_lazy_list l'))

  let concat_map f = concat -| map f
  let flatten_map = concat_map
end

module Memoize = struct
  let create_gen size =
    let tbl = Hashtbl.create size in
    fun ~found ~key_of x ~result_of f ->
      let k = key_of x in
      match Hashtbl.find_option tbl k with
      | Some x -> found x
      | None ->
          f k
          |@> Hashtbl.add tbl k -| result_of

  let create size =
    let cache = create_gen size in
    fun x f -> cache ~found:Fun.id ~key_of:Fun.id x ~result_of:Fun.id f
end

let rec fixed_point ?(eq=(=)) ?(limit= -1) f init =
  let x = f init in
  if eq x init || limit = 0
  then x
  else fixed_point ~eq ~limit:(limit-1) f x

let rec fixed_point_update ?(limit= -1) f init =
  let b,x = f init in
  if not b || limit = 0
  then x
  else fixed_point_update ~limit:(limit-1) f x


let transitive_closure ?(eq=(=)) edges =
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

let assign_id_by_eq (type t) ?(eq=(=)) ?(size=0) ?(origin=0) (xs : t list) : int * (t -> int) * (t * int) list =
  let module H = Hashtbl.Make(struct type nonrec t = t let equal = eq let hash = Hashtbl.hash end) in
  let tbl = H.create size in
  let cnt = ref origin in
  let find_and_assign x =
    try
      H.find tbl x
    with Not_found ->
      let n = !cnt in
      incr cnt;
      H.add tbl x n;
      n
  in
  let map = List.map (Pair.add_right find_and_assign) xs in
  H.length tbl,
  H.find tbl,
  map

(** Index/rank of sorted lists by topological sort
    where the element of a SCC becomes the same index.
    For example, the indices for graph [[a,b,c] -> [d] -> [e,f,g] -> [h]] ([[...]] represents a SCC)
    are [[(b, 0); (c, 0); (a, 0); (d, 1); (e, 2); (f, 2); (g, 2); (h, 3)]]. *)
let topological_index
      (scc_of : (int * int) list -> int list list)
      ?(eq = (=))
      (edges : ('a * 'a) list)
    : ('a * int) list =
  let _,id_of,map = assign_id_by_eq ~eq @@ List.rev_flatten_map Pair.to_list edges in
  let vertices = List.map snd map |> List.sort_uniq compare in
  let rev_map : (int * 'a) list  = List.map Pair.swap map in
  let edges_id : (int * int) list = List.map (Pair.map_same id_of) edges in
  let scc : int list list = scc_of edges_id in
  let repr : (int * int list) list = List.mapi Pair.pair scc in
  let repr_of x = List.find_map (fun (r, xs) -> if List.mem x xs then Some r else None) repr in
  let edges_repr : (int * int) list =
    let trans (v1,v2) =
      let r1 = repr_of v1 in
      let r2 = repr_of v2 in
      if r1 = r2 then None else Some (r1, r2)
    in
    edges_id
    |> List.filter_map trans
    |> List.sort_uniq compare
  in
  let sorted = topological_sort edges_repr in
  let sorted_comp = List.Set.(vertices - sorted) @@@ sorted in
  let idx_repr : (int * int) list = List.mapi Pair.pair_rev sorted_comp in
  repr
  |> List.rev_flatten_map (fun (r,xs) -> List.map (Pair.pair @@ List.assoc r idx_repr) xs)
  |> List.map (fun (id,x) -> List.assoc x rev_map, id)

module ProgressBar = struct
  let bars = ["▏";"▎";"▍";"▌";"▋";"▊";"▉";"█"]
  let bar_num = List.length bars

  (** 0. <= p <= 1. *)
  let make length p =
    let n = int_of_float (0.5 +. (float_of_int (length * bar_num)) *. p) in
    let last = List.last bars in
    let c1,c2 = n / 8, n mod 8 in
    let b = c1 = length in
    let s =
      String.join "" (List.make c1 last) ^
      (if b then "" else List.nth bars c2) ^
      String.make (length - c1 - (if b then 0 else 1)) ' '
    in
    n, s

  let print fm length p =
    let n,s = make length p in
    Format.fprintf fm "%3d%%|%s|\r@?" (n/bar_num) s
end

module Print_ = struct
  let int = Format.pp_print_int
  let float = Format.pp_print_float
  let char = Format.pp_print_char
  let bool = Format.pp_print_bool
  let string = Format.pp_print_string
  let option = Option.print
  let pair = Pair.print
  let ( * ) = pair
  let triple = Triple.print
  let list = List.print
  let ignore ?(str="_") fm _ = Format.pp_print_string fm str
  let __ fm x = ignore ~str:"_" fm x
  let (|>) f pr fm x = pr fm (f x) (* Format.printf "%a" (f |> pr) x = Format.printf "%a" pr (f x) *)
  let (<|) pr f fm x = pr fm (f x)
end

let pp_int = Print_.int
let pp_float = Print_.float
let pp_char = Print_.char
let pp_bool = Print_.bool
let pp_string = Print_.string
let pp_list = Print_.list
