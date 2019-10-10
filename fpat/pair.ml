open Util

(** Pairs *)

let make x1 x2 = (x1, x2)

let of_list [x1; x2] = (x1, x2)
let list_of (x1, x2) = [x1; x2]

let map f1 f2 (x1, x2) = (f1 x1, f2 x2)
let map_fst f (x1, x2) = (f x1, x2)
let map_snd f (x1, x2) = (x1, f x2)
let map2 f1 f2 (x1, x2) (y1, y2) = (f1 x1 y1, f2 x2 y2)

let fold f (x1, x2) = f x1 x2
let lift f (x1, x2) = (f x1, f x2)
let lift2 f (x1, x2) (y1, y2) = (f x1 y1, f x2 y2)
let unfold f1 f2 x = (f1 x, f2 x)

let pr epr1 epr2 ppf (x1, x2) =
  Format.fprintf ppf "@[(@[<hov>%a,@ %a@])@]" epr1 x1 epr2 x2

let flip (x1, x2) = (x2, x1)
