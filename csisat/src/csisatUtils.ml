(*
 *  CSIsat is an interpolating decision procedure for LA + EUF.
 *  This file is part of CSIsat. 
 *
 *  Copyright (C) 2007-2008  Dirk Beyer and Damien Zufferey.
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 *
 *
 *  CSIsat web page:
 *    http://www.cs.sfu.ca/~dbeyer/CSIsat/
 *)

(** General methods that are independent from other parts.
 *)

module Int =
  struct
    type t = int
    let compare = compare
  end
module IntSet = Set.Make(Int)

(** ugly method to search in an IntSet *)
let find_in_IntSet query set =
  let elt = ref None in
  let res =  IntSet.exists
    (fun x ->
      if query x then
        begin
          elt := Some x;
          true
        end
      else false
    ) set
  in
    if res then
      begin
        match !elt with
        | Some x -> x
        | None -> failwith "Utils, find_in_IntSet: found, but not found ?!"
      end
    else raise Not_found

(** Concatenates a list of string, adding a separator between 2 elements.
 * @param sep the separator
 * @param lst the list to concatenate
 *)
let string_list_cat sep lst =
  let buffer = Buffer.create 10 in
  let rec process lst = match lst with
    | x :: [] -> Buffer.add_string buffer x
    | x :: xs -> Buffer.add_string buffer x; Buffer.add_string buffer sep; process xs
    | [] -> ()
  in
    process lst;
    Buffer.contents buffer

(** Print a float and removes trailing '.'.
 *)
let my_string_of_float flt =
  let (f,i) = modf flt in
    if f = 0.0 then string_of_int (int_of_float i)
    else string_of_float flt

(** Returns the minimum x of query_fct(x) for x in lst.
 * Assume that lst has at least one element.
 *)
let min_of_list query_fct lst =
  let min_term = ref (List.hd lst) in
  let min_val = ref (query_fct (List.hd lst)) in
    List.iter (fun x ->
        let v = query_fct x in
          if v < !min_val then
            begin
              min_term := x;
              min_val := v
            end
      ) lst;
    !min_term

(** Removes the Some of an option *)
let remove_some lst =
  List.map
    (fun x -> match x with
      | Some x -> x
      | None -> failwith "remove_some found a None"
    ) lst

(** splits a list after position n.*)
let split_list n lst =
  let acc = ref [] in
  let rec process n lst = match lst with
    | (x::xs) as lst ->
      if n > 0 then
        begin
          acc := x::!acc;
          process (n-1 ) xs
        end
      else lst
    | [] -> []
  in
  let tail = process n lst in
    (List.rev !acc, tail)

(** map + keep only elements y where fct(x) = Some(y)*)
let rec map_filter fct lst = match lst with
  | x::xs ->
    begin
      match fct x with
      | Some r -> r::(map_filter fct xs)
      | None -> map_filter fct xs
    end
  | [] -> []

let rev_flatten lst = 
  List.fold_left (fun acc x -> List.rev_append x acc) [] lst

(*from a list of edges (pairs) to a adjacency hashtbl*)
let edges_to_graph edges =
  let graph = Hashtbl.create 53 in
    List.iter 
      ( fun (x,y) ->
        let already =
          try Hashtbl.find graph x
          with Not_found -> []
        in
          Hashtbl.replace graph x (y::already);
          if not (Hashtbl.mem graph y) then Hashtbl.add graph y []
      ) edges;
    graph

let edges_to_graph_not_directed edges =
  let graph = Hashtbl.create 53 in
    List.iter 
      ( fun (x,y) ->
        let alreadyx =
          try Hashtbl.find graph x
          with Not_found -> []
        in
        let alreadyy =
          try Hashtbl.find graph y
          with Not_found -> []
        in
          Hashtbl.replace graph x (y::alreadyx);
          Hashtbl.replace graph y (x::alreadyy)
      ) edges;
    graph

(* build the list of primes *)
let prime_list n =
  let rec is_prime lst_prime x =
    match lst_prime with
    | p::ps ->
      if (x mod p) = 0 then
        false
      else
		    if p*p > x then
		      true
		    else
          is_prime ps x
    | [] -> true
  in
    let rec build_list acc i =
      if i > n then
        acc
      else
        begin
          if is_prime acc i then
            build_list (i::acc) (i+1)
          else
            build_list acc (i+1)
        end
    in
      build_list [] 2

(** gives the prime number decomposition of a number.
 * assume n is positive.
 *)
let factorise n = 
  if n = 1 then [1] (*!!!*)
  else
    begin
      let primes = List.rev (prime_list (int_of_float (sqrt (float_of_int n)))) in
        let c = ref n in
        let rec iter acc x =
          match x with
          | [] -> acc
          | y::ys ->
              if (!c mod y) = 0 then
                begin
                  c := !c / y;
                  iter (y::acc) x
                end
              else
                iter acc ys
         in
          let result = iter [] primes in
            if !c <> 1 then
              !c :: result
            else
              result
    end

(** power of integers.
 *  Assume exponent to be >= 0
 *)
let power base exponent =
  assert (exponent >= 0);
  let rec pow acc base exponent = 
    if exponent = 0 then acc
    else if (exponent mod 2) = 0 then pow acc (base * base) (exponent / 2)
    else
      begin
       assert ((exponent mod 2) = 1); 
       pow (acc * base) base (exponent -1)
      end
  in
    pow 1 base exponent

let round n =
  let (f,i) = modf n in
    if f < (-0.5) then i -. 1.
    else if f >= 0.5 then i +. 1.
    else i

let cartesian_product l1 l2 =
  List.flatten (List.map (fun x -> List.map (fun y -> (x,y)) l2) l1)
