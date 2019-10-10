open Util

(** Ordered environment *)
module type KEY = sig
  type t
  val compare : t -> t -> int
  val print : Format.formatter -> t -> unit
end

module type VALUE = sig
  type t
  val print : Format.formatter -> t -> unit
  val merge : t -> t -> t list
  val eq : t -> t -> bool
end

module type ENV = sig
  type t
  type key
  type value
  val empty : t
  val add : key -> value -> t -> t
  val create : (key -> value) -> key list -> t

  val of_list : (key * value) list -> t
  val to_list : t -> (key * value) list
  val keys : t -> key list
  val values : t -> value list
  val dom : t -> key list
  val cod : t -> value list
  val codom : t -> value list
  val range : t -> value list

  val find : (key * value -> bool) -> t -> key * value
  val assoc : key -> t -> value
  val mem_assoc : key -> t -> bool
  val assoc_option : key -> t -> value option
  val assoc_all : key -> t -> value list

  val map : (key * value -> key * value) -> t -> t
  val map_key : (key -> key) -> t -> t
  val map_value : (value -> value) -> t -> t
  val filter : (key -> value -> bool) -> t -> t
  val filter_key : (key -> bool) -> t -> t
  val filter_value : (value -> bool) -> t -> t
  val filter_out : (key -> value -> bool) -> t -> t
  val filter_key_out : (key -> bool) -> t -> t
  val filter_value_out : (value -> bool) -> t -> t
  val merge : t -> t -> t
  val normalize : t -> t

  val eq : t -> t -> bool
  val exists : (key -> value -> bool) -> t -> bool
  val for_all : (key -> value -> bool) -> t -> bool

  val print : Format.formatter -> t -> unit
end

module Make (Key : KEY) (Value : VALUE) : ENV with type key := Key.t with type value := Value.t
=
struct
  type t = (Key.t * Value.t) list

  let eq_key k1 k2 = Key.compare k1 k2 = 0

  let empty = []
  let add k x env = (k,x)::env
  let create f keys = List.fold_right (fun x env -> add x (f x) env) keys empty

  let of_list env = env
  let to_list env = env
  let keys env = List.map fst env
  let values env = List.map snd env
  let dom = keys
  let cod = values
  let codom = values
  let range = values

  let find f env = List.find f env
  let assoc k env = List.assoc ~eq:eq_key k env
  let mem_assoc k env = List.mem_assoc ~eq:eq_key k env
  let assoc_option k env = List.assoc_option ~eq:eq_key k env
  let assoc_all k env = List.assoc_all ~eq:eq_key k env

  let map f env = List.map f env
  let map_key f env = List.map (Pair.map_fst f) env
  let map_value f env = List.map (Pair.map_snd f) env
  let filter f env = List.filter (Fun.uncurry f) env
  let filter_key f env = List.filter (fst |- f) env
  let filter_value f env = List.filter (snd |- f) env
  let filter_out f env = List.filter_out (Fun.uncurry f) env
  let filter_key_out f env = List.filter_out (fst |- f) env
  let filter_value_out f env = List.filter_out (snd |- f) env
  let merge env1 env2 =
    let aux (k,x) acc =
      if mem_assoc k acc then
        List.flatten_map (fun (k',x') -> let xs = if eq_key k k' then Value.merge x x' else [x'] in List.map (fun y -> k', y) xs) acc
      else
        (k,x)::acc
    in
    List.fold_right aux env1 env2
  let normalize env =
    List.fold_right (fun v acc -> merge [v] acc) env []

  let rec eq env1 env2 =
    match env1 with
    | [] -> env2 = []
    | (k,x)::env1' ->
        let b,env2' =
          try
            let x',env2' = List.decomp_assoc k env2 in
            Value.eq x x', env2'
          with Not_found -> false, []
        in
        b && eq env1' env2'

  let exists f env = List.exists (Fun.uncurry f) env
  let for_all f env = List.for_all (Fun.uncurry f) env

  let print fm env =
    let pr fm (k,x) = Format.fprintf fm "@[%a |-> %a@]" Key.print k Value.print x in
    List.print pr fm env
end
