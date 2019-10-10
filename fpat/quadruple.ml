open Util

(** Quadruples *)

let make x1 x2 x3 x4 = (x1, x2, x3, x4)

let of_list [x1; x2; x3; x4] = (x1, x2, x3, x4)
let list_of (x1, x2, x3, x4) = [x1; x2; x3; x4]

let fst (x1, x2, x3, x4) = x1
let snd (x1, x2, x3, x4) = x2
let trd (x1, x2, x3, x4) = x3
let fth (x1, x2, x3, x4) = x4

let get12 (x1, x2, x3, x4) = (x1, x2)
let get13 (x1, x2, x3, x4) = (x1, x3)
let get14 (x1, x2, x3, x4) = (x1, x4)
let get21 (x1, x2, x3, x4) = (x2, x1)
let get23 (x1, x2, x3, x4) = (x2, x3)
let get24 (x1, x2, x3, x4) = (x2, x4)
let get31 (x1, x2, x3, x4) = (x3, x1)
let get32 (x1, x2, x3, x4) = (x3, x2)
let get34 (x1, x2, x3, x4) = (x3, x4)
let get41 (x1, x2, x3, x4) = (x4, x1)
let get42 (x1, x2, x3, x4) = (x4, x2)
let get43 (x1, x2, x3, x4) = (x4, x3)

let get123 (x1, x2, x3, x4) = (x1, x2, x3)
let get124 (x1, x2, x3, x4) = (x1, x2, x4)
let get132 (x1, x2, x3, x4) = (x1, x3, x2)
let get134 (x1, x2, x3, x4) = (x1, x3, x4)
let get142 (x1, x2, x3, x4) = (x1, x4, x2)
let get143 (x1, x2, x3, x4) = (x1, x4, x3)
let get213 (x1, x2, x3, x4) = (x2, x1, x3)
let get214 (x1, x2, x3, x4) = (x2, x1, x4)
let get231 (x1, x2, x3, x4) = (x2, x3, x1)
let get234 (x1, x2, x3, x4) = (x2, x3, x4)
let get241 (x1, x2, x3, x4) = (x2, x4, x1)
let get243 (x1, x2, x3, x4) = (x2, x4, x3)
let get312 (x1, x2, x3, x4) = (x3, x1, x2)
let get314 (x1, x2, x3, x4) = (x3, x1, x4)
let get321 (x1, x2, x3, x4) = (x3, x2, x1)
let get324 (x1, x2, x3, x4) = (x3, x2, x4)
let get341 (x1, x2, x3, x4) = (x3, x4, x1)
let get342 (x1, x2, x3, x4) = (x3, x4, x2)
let get412 (x1, x2, x3, x4) = (x4, x1, x2)
let get413 (x1, x2, x3, x4) = (x4, x1, x3)
let get421 (x1, x2, x3, x4) = (x4, x2, x1)
let get423 (x1, x2, x3, x4) = (x4, x2, x3)
let get431 (x1, x2, x3, x4) = (x4, x3, x1)
let get432 (x1, x2, x3, x4) = (x4, x3, x2)

let map f1 f2 f3 f4 (x1, x2, x3, x4) = (f1 x1, f2 x2, f3 x3, f4 x4)
let map_fst f (x1, x2, x3, x4) = (f x1, x2, x3, x4)
let map_snd f (x1, x2, x3, x4) = (x1, f x2, x3, x4)
let map_trd f (x1, x2, x3, x4) = (x1, x2, f x3, x4)
let map_fth f (x1, x2, x3, x4) = (x1, x2, x3, f x4)

let fold f (x1, x2, x3, x4) = f x1 x2 x3 x4
let lift f (x1, x2, x3, x4) = (f x1, f x2, f x3, f x4)
let unfold f1 f2 f3 f4 x = (f1 x, f2 x, f3 x, f4 x)

let pr epr1 epr2 epr3 epr4 ppf (x1, x2, x3, x4) =
  Format.fprintf ppf
    "(@[<hov>%a,@ %a,@ %a,@ %a@])"
    epr1 x1 epr2 x2 epr3 x3 epr4 x4
