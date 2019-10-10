open Combinator

(** Utility functions *)

module Format = struct
  include Format

  let printf_force fmt = printf fmt
  let iprintf fmt = ifprintf std_formatter fmt
  let printf fmt = if !Global.silent then iprintf fmt else printf fmt
  let pprintf fmt x = printf fmt x; x
end

(** Strings *)
module String = struct
  include BatString

  let pr ppf str = Format.fprintf ppf "%s" str

  let is_int s = try let _ = int_of_string s in true with Failure _ -> false
  let is_float s = try let _ = float_of_string s in true with Failure _ -> false

  (** @todo sufficient for identifiers of OCaml? *)
  let escape s = map (fun c -> if c = '.' || c = '!' then '_' else c) s

  let split_at i str =
    if i < 0
    then "", str
    else if i > String.length str then str, ""
    else String.sub str 0 i, String.sub str i (String.length str - i)
end

(** Lists *)
module List = struct
  include BatList

  (** {6 Auxiliary constructors} *)

  let cons x xs = x :: xs
  let return x = [x]

  (** {6 Auxiliary destructors} *)

  let rec delete p = function
    | [] -> []
    | x :: xs' -> if p x then xs' else x :: delete p xs'

  let hd_tl = function [] -> assert false | x :: xs' -> (x, xs')

  let rec initial_last = function
    | [] -> assert false
    | [x] -> [], x
    | x :: xs' -> let ys, y = initial_last xs' in (x :: ys, y)

  let non_nil_list_of = function [] -> assert false | xs -> xs

  let elem_of_singleton = function
    | [x] -> x
    | xs ->
      Format.printf "an error in elem_of_singleton: %d@," (length xs);
      assert false

  (** {6 Inspectors} *)

  let rec mem ?(cmp = (=)) x = function
    | [] -> false
    | x' :: xs' -> cmp x x' || mem ~cmp:cmp x xs'

  let eq_length l1 l2 = length l1 = length l2

  let rec is_prefix xs ys =
    match xs, ys with
    | [], _ -> true
    | x :: xs', y :: ys' -> x = y && is_prefix xs' ys'
    | _, _ -> false

  let all_equiv eqrel = function
    | [] -> true
    | x :: xs -> for_all (fun x' -> eqrel x x') xs

  let rec assoc_inverse asso x =
    match asso with
    | [] -> assert false
    | (i, xs) :: rest ->
      try i, findi (curry2 (snd >> (=) x)) xs |> fst
      with Not_found -> assoc_inverse rest x
  let assoc_fail ?(on_failure = fun () -> ()) x xs =
    try assoc x xs with Not_found -> on_failure (); assert false
  let assocF = assoc_fail
  let assoc_default d x xs = try assoc x xs with Not_found -> d
  let assocD = assoc_default

  (** {6 Searching operators} *)

  let find_fail ?(on_failure = fun () -> ()) p xs =
    try find p xs with Not_found -> on_failure (); assert false
  let rec find_map f = function
    | [] -> raise Not_found
    | x :: xs' -> match f x with None -> find_map f xs' | Some(y) -> y

  (* aka pick
     let findlr p xs =
     let rec aux l r =
      match r with
      | [] -> raise Not_found
      | x :: r' ->
        if p x then l, x, r' else aux (l @ [x]) r'
     in
     aux [] xs*)

  let find_mapi f xs =
    let rec aux i = function
      | [] -> raise Not_found
      | x :: xs' ->
        match f i x with None -> aux (i + 1) xs' | Some(y) -> i, y
    in
    aux 0 xs

  let find_maplr f xs =
    let rec aux l r =
      match r with
      | [] -> raise Not_found
      | x :: r' ->
        match f l x r' with None -> aux (l @ [x]) r' | Some(y) -> y
    in
    aux [] xs

  let filteri p xs =
    let rec aux i = function
      | [] -> []
      | x :: xs' ->
        if p i x then x :: aux (i + 1) xs' else aux (i + 1) xs'
    in
    aux 0 xs

  let rec filter_map2 f xs ys =
    match xs, ys with
    | [], [] -> []
    | x :: xs', y :: ys' ->
      begin
        match f x y with
        | None -> filter_map2 f xs' ys'
        | Some(r) -> r :: filter_map2 f xs' ys'
      end
    | _ -> assert false

  let filter_mapLr f xs =
    let rec aux l r =
      match r with
      | [] -> l
      | x :: r' ->
        match f l x r' with
        | None -> aux l r'
        | Some(x') -> aux (l @ [x']) r'
    in
    aux [] xs

  let partition_map f ys =
    let rec aux xs = fun ls rs ->
      match xs with
      | [] -> ls, rs
      | x :: xs' ->
        match f x with
        | `L(y) -> aux xs' (y :: ls) rs
        | `R(y) -> aux xs' ls (y :: rs)
        | _ -> failwith "Util.List.partition_map"
    in
    aux (rev ys) [] []

  let partition3_map f ys =
    let rec aux xs = fun ls cs rs ->
      match xs with
      | [] -> ls, cs, rs
      | x :: xs' ->
        match f x with
        | `L(y) -> aux xs' (y :: ls) cs rs
        | `C(y) -> aux xs' ls (y :: cs) rs
        | `R(y) -> aux xs' ls cs (y :: rs)
        | _ -> failwith "Util.List.partition3_map"
    in
    aux (rev ys) [] [] []

  (** {6 Printers} *)

  let rec pr_aux epr sep i ppf = function
    | [] -> ()
    | [x] -> epr ppf (i, x)
    | x :: xs' ->
      Format.fprintf ppf "%a%a%a"
        epr (i, x) Format.fprintf sep (pr_aux epr sep (i + 1)) xs'

  let pr epr ?(header="") ?(footer="") sep ppf xs =
    Format.fprintf ppf "%s@[<v>%a@]%s"
      header (pr_aux (fun ppf (_, x) -> epr ppf x) sep 0) xs footer

  let pri epr sep ppf xs =
    Format.fprintf ppf "@[<v>%a@]" (pr_aux epr sep 0) xs

  let pr_hov epr sep ppf xs =
    Format.fprintf ppf "@[<hov>%a@]"
      (pr_aux (fun ppf (_, x) -> epr ppf x) sep 0) xs

  let pr_ocaml epr ppf xs =
    Format.fprintf ppf "[@[<v>%a@]]"
      (pr_aux (fun ppf (_, x) -> epr ppf x) "; " 0) xs

  let pr_app epr sep ppf = function
    | [] -> ()
    | [x] -> epr ppf x
    | x :: xs ->
      Format.fprintf ppf "@[<hov2>%a@ @[<hov>%a@]@]"
        epr x (pr_aux (fun ppf (_, x) -> epr ppf x) sep 0) xs

  let print_list epr sep = pr epr sep Format.std_formatter

  let rec pr_string_separator epr sep ppf = function
    | [] -> ()
    | [x] -> epr ppf x
    | x :: xs' ->
      Format.fprintf ppf "%a%s%a" epr x sep (pr_string_separator epr sep) xs'

  (** {6 Iterators} *)

  let iter2i f =
    let rec aux i xs ys=
      match xs, ys with
      | [], [] -> ()
      | x :: xs', y :: ys' -> f i x y; aux (i + 1) xs' ys'
      | _ -> assert false
    in
    aux 0

  let rec iter3 f xs ys zs =
    match xs, ys, zs with
    | [], [], [] -> ()
    | x :: xs', y :: ys', z :: zs' -> f x y z; iter3 f xs' ys' zs'
    | _ -> assert false

  let iter3i f =
    let rec aux i xs ys zs=
      match xs, ys, zs with
      | [], [], [] -> ()
      | x :: xs', y :: ys', z :: zs' ->
        f i x y z;
        aux (i + 1) xs' ys' zs'
      | _ -> assert false
    in
    aux 0

  (** {6 Zipping and unzipping operators} *)

  let zip = combine

  let rec zip3 xs ys zs =
    match xs, ys, zs with
    | [], [], [] -> []
    | x :: xs', y :: ys', z :: zs' -> (x, y, z) :: zip3 xs' ys' zs'
    | _ -> assert false

  let unzip = split

  let rec unzip3 ls =
    match ls with
    | [] -> [], [], []
    | (x, y, z) :: ls ->
      let (xs, ys, zs) = unzip3 ls in
      x :: xs, y :: ys, z :: zs
  let split3 = unzip3

  (** {6 Concatenation operators} *)

  let rec concat_opt = function
    | [] -> []
    | None :: xs' -> concat_opt xs'
    | Some(x) :: xs' -> x :: concat_opt xs'

  let concat_unzip xs = let ls, rs = unzip xs in concat ls, concat rs

  let concat_map f =
    let rec aux a = function
      | [] -> a
      | x :: xs' -> let r = f x in aux (a @ r) xs'
    in
    aux []

  let concat_mapi f =
    let rec aux i a = function
      | [] -> a
      | x :: xs' -> let r = f i x in aux (i + 1) (a @ r) xs'
    in
    aux 0 []

  let concat_rev_map f xs =
    List.fold_left (fun acc x -> List.rev_append (f x) acc) [] xs

  let rec concat_map2 f xs ys =
    match xs, ys with
    | [], [] -> []
    | x :: xs', y :: ys' ->
      let r = f x y in
      let rs = concat_map2 f xs' ys' in
      r @ rs
    | _ -> assert false

  let concat_map2i f =
    let rec aux i a xs ys =
      match xs, ys with
      | [], [] -> a
      | x :: xs', y :: ys' ->
        let r = f i x y in
        aux (i + 1) (a @ r) xs' ys'
      | _ -> assert false
    in
    aux 0 []

  let rec concat_map3 f xs ys zs =
    match xs, ys, zs with
    | [], [], [] -> []
    | x :: xs', y :: ys', z :: zs' ->
      let r = f x y z in
      let rs = concat_map3 f xs' ys' zs' in
      r @ rs
    | _ -> assert false

  let concat_map3i f =
    let rec aux i xs ys zs =
      match xs, ys, zs with
      | [], [], [] -> []
      | x :: xs', y :: ys', z :: zs' ->
        let r = f i x y z in
        let rs = aux (i + 1) xs' ys' zs' in
        r @ rs
      | _ -> assert false
    in
    aux 0

  (** {6 Sorting operators} *)

  let sort_by f xs =
    xs
    |> map (fun x -> f x, x)
    |> sort (fun (n1, _) (n2, _) -> n1 - n2)
    |> map snd
  let sort_dec_by f xs =
    xs
    |> map (fun x -> f x, x)
    |> sort (fun (n1, _) (n2, _) -> n2 - n1)
    |> map snd

  (** {6 Operators for sublists} *)

  (** @require xs is not empty
      @return xs without the last element *)
  let rec initial = function
    | [] -> assert false
    | [x] -> []
    | x :: xs' -> x :: initial xs'

  (** \[1; 2; 3\] = \[\[\]; \[1\]; \[1; 2\]; \[1; 2; 3\]\] *)
  let inits xs =
    xs
    |> (fold_left
          (fun (prefix, prefixes) x ->
             let prefix' = prefix @ [x] in
             prefix', prefixes @ [prefix'])
          ([], [[]]))
    |> snd


  (*let rec split_at n xs =
    if n < 0 then failwith "split_at"
    else if n = 0 then [], xs
    else
      let x :: xs' = xs in
      let ls, rs = split_at (n - 1) xs' in
      x::ls, rs*)
  let split_at = split_nth

  let rec split_by_list ls xs =
    match ls with
    | [] -> [xs]
    | l :: ls' ->
      let xs1, xs2 = split_at l xs in
      xs1 :: split_by_list ls' xs2

  let rec span p = function
    | [] -> [], []
    | x :: xs' ->
      if p x then
        let ls, rs = span p xs' in
        x :: ls, rs
      else [], x :: xs'

  let rec span_map f = function
    | [] -> [], []
    | x :: xs' ->
      match f x with
      | None -> [], x :: xs'
      | Some(y) -> let ls, rs = span_map f xs' in y :: ls, rs

  let rec break p = function
    | [] -> [], []
    | x :: xs' ->
      if p x
      then [], x :: xs'
      else let ls, rs = break p xs' in x :: ls, rs

  let breaklr p xs =
    let rec aux l r =
      match r with
      | [] -> [], []
      | x :: r' -> if p l x r' then l, r else aux (l @ [x]) r
    in
    aux [] xs

  let pick p xs =
    xs |> break p
    |> (function _, [] -> raise Not_found | l, x :: r -> l, x, r)
  let picklr p xs =
    xs |> breaklr p
    |> (function _, [] -> raise Not_found | l, x :: r -> l, x, r)

  let rec pick_map f = function
    | [] -> raise Not_found
    | x :: xs' ->
      match f x with
      | None ->
        let ls, y, rs = pick_map f xs' in
        x :: ls, y, rs
      | Some(y) -> [], y, xs'

  let rec pick_maplr f xs =
    let rec aux l r =
      match r with
      | [] -> raise Not_found
      | x :: r' ->
        match f l x r' with
        | None -> aux (l @ [x]) r'
        | Some(y) -> l, y, r'
    in
    aux [] xs

  (** {6 Classification operators} *)

  let rec classify eqrel = function
    | [] -> []
    | x :: xs' ->
      let t, f = partition (eqrel x) xs' in
      (x :: t) :: (classify eqrel f)

  (** {6 Shuffling operators} *)

  let shuffle xs =
    let xs = map (fun x -> Random.int 65536, x) xs in
    map snd (fast_sort (fun (r1, _) (r2, _) -> r1 - r2) xs)

  (** {6 Indexing operators} *)

  let apply_at i f xs =
    let l, x :: r = split_at i xs in
    l @ f x :: r

  let replace_at i x = apply_at i (fun _ -> x)

  (** {6 Operators for list contexts} *)

  let rec context_of i = function
    | [] -> assert false
    | x :: xs' ->
      if i = 0 then fun ys -> ys @ xs'
      else if i > 0 then
        let ctx = context_of (i - 1) xs' in
        fun ys -> x :: ctx ys
      else assert false

  (** {6 Mapping operators} *)

  let rec map3 f xs ys zs =
    match xs, ys, zs with
    | [], [], [] -> []
    | x :: xs', y :: ys', z :: zs' -> f x y z :: map3 f xs' ys' zs'
    | _ -> assert false
  let rec map4 f xs ys zs ws =
    match xs, ys, zs, ws with
    | [], [], [], [] -> []
    | x :: xs', y :: ys', z :: zs', w :: ws' ->
      f x y z w :: map4 f xs' ys' zs' ws'
    | _ -> assert false
  let map3i f =
    let rec aux i xs ys zs =
      match xs, ys, zs with
      | [], [], [] -> []
      | x :: xs', y :: ys', z :: zs' ->
        f i x y z :: aux (i + 1) xs' ys' zs'
      | _ -> assert false
    in
    aux 0
  let map4i f =
    let rec aux i xs ys zs ws =
      match xs, ys, zs, ws with
      | [], [], [], [] -> []
      | x :: xs', y :: ys', z :: zs', w :: ws' ->
        f i x y z w :: aux (i + 1) xs' ys' zs' ws'
      | _ -> assert false
    in
    aux 0
  let mapc f xs = mapi (fun i x -> f (context_of i xs) x) xs

  let maplr f xs =
    let rec aux l r =
      match r with
      | [] -> []
      | x :: r' -> f l x r' :: aux (l @ [x]) r'
    in
    aux [] xs

  let mapLr f xs =
    let rec aux l r =
      match r with
      | [] -> l
      | x :: r' -> let y = f l x r' in aux (l @ [y]) r'
    in
    aux [] xs

  let maplR f xs =
    let rec aux l r =
      match l with
      | [] -> r
      | x :: l' -> let y = f (rev l') x r in aux l' (y :: r)
    in
    aux (rev xs) []

  (* similar to Data.List.mapAccumL in Haskell *)
  let mapLar f a xs =
    let rec aux l a r =
      match r with
      | [] -> l, a
      | x :: r' -> let y, a' = f l a x r' in aux (l @ [y]) a' r'
    in
    aux [] a xs

  (* similar to Data.List.mapAccumR in Haskell *)
  let maplaR f xs a =
    let rec aux l a r =
      match l with
      | [] -> a, r
      | x :: l' -> let a', y = f (rev l') x a r in aux l' a' (y :: r)
    in
    aux (rev xs) a []

  (** {6 Folding operators} *)

  let fold_lefti f a xs =
    let rec aux i a = function
      | [] -> a
      | x :: xs' -> aux (i + 1) (f i a x) xs'
    in
    aux 0 a xs

  let rec scan_left f a = function
    | [] -> [a]
    | x :: xs' -> a :: scan_left f (f a x) xs'

  let rec scan_right f xs a =
    match xs with
    | [] -> [a]
    | x :: xs' ->
      let b :: bs = scan_right f xs' a in
      f x b :: b :: bs

  (** {6 Generating operators} *)

  let gen n f =
    let rec aux i = if i >= n then [] else f i :: aux (i + 1) in
    aux 0

  let rec unfold f seed =
    match f seed with
    | None -> []
    | Some(x, seed') -> x :: unfold f seed'

  let from_to s e =
    unfold (fun i -> if i <= e then Some(i, i + 1) else None) s

  let duplicate x size =
    unfold (fun i -> if i < size then Some(x, i + 1) else None) 0

  let prefixes xs =
    map (fun n -> take n xs) (from_to 0 (List.length xs))

  (** {6 Unclassified operators} *)

  let split_map f xs = split (map f xs)
  let split_mapi f xs = split (mapi f xs)
end

(** Arrays *)
module Array = struct
  include Array

  let unzip ar = map fst ar, map snd ar
end

(** Filenames *)
module Filename = struct
  include Filename

  let get_extension fullname =
    let name = Filename.chop_extension fullname in
    let fullname_len, name_len =
      (String.length fullname, String.length name)
    in
    String.sub fullname name_len (fullname_len - name_len)
end
