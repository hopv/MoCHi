type t = Ip | Im | O

let cmp tg1 tg2 =
  match tg1, tg2 with
  | Im, Im -> 0
  | Im, Ip -> -1
  | Im, O -> -1
  | Ip, Im -> 1
  | Ip, Ip -> 0
  | Ip, O -> -1
  | O, Im -> 1
  | O, Ip -> 1
  | O, O -> 0
