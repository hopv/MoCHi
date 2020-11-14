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

(** Central module to manage the output.
 * For the sake of efficiency, the string arguments are lazy.
 * Therefore when the debug output is not activated,
 * the debug messages are not evaluated.
 *)

let debug = ref false
let enable_debug () = debug := true

type msg = Debug | Normal | Error

let print m str = match m with 
  | Debug -> if !debug then print_endline (Lazy.force str)
  | Normal -> print_endline (Lazy.force str)
  | Error -> prerr_endline (Lazy.force str)
