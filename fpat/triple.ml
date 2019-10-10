open Util

(** Triples *)

let make x1 x2 x3 = (x1, x2, x3)

let of_list [x1; x2; x3] = (x1, x2, x3)
let list_of (x1, x2, x3) = [x1; x2; x3]

let fst (x1, x2, x3) = x1
let snd (x1, x2, x3) = x2
let trd (x1, x2, x3) = x3

let get12 (x1, x2, x3) = (x1, x2)
let get13 (x1, x2, x3) = (x1, x3)
let get21 (x1, x2, x3) = (x2, x1)
let get23 (x1, x2, x3) = (x2, x3)
let get31 (x1, x2, x3) = (x3, x1)
let get32 (x1, x2, x3) = (x3, x2)

let get123 (x1, x2, x3) = (x1, x2, x3)
let get132 (x1, x2, x3) = (x1, x3, x2)
let get213 (x1, x2, x3) = (x2, x1, x3)
let get231 (x1, x2, x3) = (x2, x3, x1)
let get312 (x1, x2, x3) = (x3, x1, x2)
let get321 (x1, x2, x3) = (x3, x2, x1)

let map f1 f2 f3 (x1, x2, x3) = (f1 x1, f2 x2, f3 x3)
let map_fst f (x1, x2, x3) = (f x1, x2, x3)
let map_snd f (x1, x2, x3) = (x1, f x2, x3)
let map_trd f (x1, x2, x3) = (x1, x2, f x3)

let fold f (x1, x2, x3) = f x1 x2 x3
let lift f (x1, x2, x3) = (f x1, f x2, f x3)
let unfold f1 f2 f3 x = (f1 x, f2 x, f3 x)

let pr epr1 epr2 epr3 ppf (x1, x2, x3) =
  Format.fprintf
    ppf
    "(@[<hov>%a,@ %a,@ %a@])"
    epr1 x1
    epr2 x2
    epr3 x3
