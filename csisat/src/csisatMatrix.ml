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

(** Matrix (array of array) processing. *)
(**/**)
module Ast = CsisatAst
(**/**)

let matrix_times_vector matrix vector =
  let row = Array.length matrix in
  let col = Array.length matrix.(0) in
  Array.init row (fun r -> 
    let acc = ref 0.0 in
      for i = 0 to col - 1 do
        acc := !acc +. (matrix.(r).(i) *. vector.(i))
      done;
      !acc
    )

let matrix_times_matrix matrixA matrixB =
  let row = Array.length matrixA in
  let col = Array.length matrixB.(0) in
  let n = Array.length  matrixA.(0) in
  let result = Array.make_matrix row col 0.0 in
    for x = 0 to row -1 do
      for y = 0 to col -1 do
        let acc = ref 0.0 in
          for k = 0 to n -1 do
            acc := !acc +. (matrixA.(x).(k) *. matrixB.(k).(y))
          done;
          result.(x).(y) <- !acc
      done
    done;
    result


let vector_times_matrix vector matrix =
  let row = Array.length matrix in
  let col = Array.length matrix.(0) in
  Array.init col (fun c -> 
    let acc = ref 0.0 in
      for i = 0 to row - 1 do
        acc := !acc +. (matrix.(i).(c) *. vector.(i))
      done;
      !acc
    )

let row_vect_times_col_vect a b =
  let col = Array.length a in
  let acc = ref 0.0 in
    for i = 0 to col - 1 do
      acc := !acc +. (a.(i) *. b.(i))
    done;
    !acc

let transpose matrix =
  let row = Array.length matrix in
  let col = Array.length matrix.(0) in
  Array.init col (fun y -> Array.init row (fun x -> matrix.(x).(y)))

let symbolic_vector_multiplication coeffs vars =
  let rec iter index acc vars = match vars with
    | x::xs -> iter (index + 1) ((Ast.Coeff(coeffs.(index),x))::acc) xs
    | [] -> acc
  in
    Ast.Sum (iter 0 [] vars)

let vector_substract a b =
  let size = Array.length a in
  let res = Array.make size 0.0 in
    for i = 0 to size - 1 do
      res.(i) <- (a.(i) -. b.(i))
    done;
    res

let string_of_col_vector vector =
  let col = Array.length vector in
  let buffer = Buffer.create (3 * col) in
    for i = 0 to col - 2 do
      Buffer.add_string buffer (string_of_float vector.(i));
      Buffer.add_char buffer '\n'
    done;
    Buffer.add_string buffer (string_of_float vector.(col -1));
    Buffer.contents buffer
  
let string_of_row_vector vector =
  let row = Array.length vector in
  let buffer = Buffer.create (3 * row) in
    for i = 0 to row - 1 do
      Buffer.add_string buffer (string_of_float vector.(i));
      Buffer.add_char buffer ' '
    done;
    Buffer.contents buffer


let string_of_matrix matrix =
  let row = Array.length matrix in
  let col = Array.length matrix.(0) in
  let buffer = Buffer.create (3 * col * row) in
    for x = 0 to row -1 do
      for y = 0 to col -1 do
        Buffer.add_string buffer (string_of_float matrix.(x).(y));
        Buffer.add_char buffer ' '
      done;
      Buffer.add_char buffer '\n'
    done;
    Buffer.contents buffer
