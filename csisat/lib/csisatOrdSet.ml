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

(***************** ORDSETS ********************)
(** Ordered sets represented as lists.
 * This module is inspired from the Sicstus/SWI prolog library with the same name.
 *)
  
let remove_duplicates lst =
  let rec process last acc lst = match lst with
    | x::xs ->
      begin
        if x <> last then process x (x::acc) xs
        else process last acc xs
      end
    | [] -> List.rev acc
  in
    match lst with
    | x::[] -> [x]
    | x::xs -> process x [x] xs
    | [] -> []

let subtract a b =
  let rec process acc a b = match (a,b) with
    | (a,[]) -> (List.rev acc)@a
    | ([],_) -> (List.rev acc)
    | (a::sa, b::bs) ->
      begin
        if a < b then process (a::acc) sa (b::bs)
        else if a > b then process acc (a::sa) bs
        else process acc sa (b::bs)
      end
  in
    process [] a b

let union a b =
  let rec process acc a b = match (a,b) with
    | (a,[]) -> (List.rev acc)@a
    | ([],b) -> (List.rev acc)@b
    | (a::sa, b::bs) ->
      begin
        if a < b then process (a::acc) sa (b::bs)
        else if a > b then process (b::acc) (a::sa) bs
        else process (a::acc) sa bs
      end
  in
    process [] a b

let intersection a b =
  let rec process acc a b = match (a,b) with
    | (_,[]) -> (List.rev acc)
    | ([],_) -> (List.rev acc)
    | (a::sa, b::bs) ->
      begin
        if a < b then process acc sa (b::bs)
        else if a > b then process acc (a::sa) bs
        else process (a::acc) sa bs
      end
  in
    process [] a b

let rec mem el lst = match lst with
  | [] -> false
  | x::xs ->
    begin
        if x < el then mem el xs
        else if x > el then  false
        else true
    end

let list_to_ordSet lst = remove_duplicates (List.sort compare lst)

