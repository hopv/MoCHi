let (|>) x f = f x

let concat_map f l = l |> (List.map f) |> List.concat

let rec fold_left3 f acc xs ys zs =
  match (xs, ys, zs) with
    | (x::xs2, y::ys2, z::zs2) -> fold_left3 f (f acc x y z) xs2 ys2 zs2
    | ([], [], []) -> acc
    | _ -> raise (Invalid_argument "fold_left3")

let first f (a, b) = (f a, b)
let second f (a, b) = (a, f b)

let update_assoc (key, cycle, value) associates =
  (key, (cycle, value)) :: (List.remove_assoc key associates)
