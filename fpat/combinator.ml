(** Combinators *)

(** {6 Basic} *)

(** identity function *)
let id x = x

(** constant function *)
let const c _ = c

(** {6 Fixed-point} *)

(** [fix f eq x] computes the fixed point of [f] modulo [eq] from [x] *)
let rec fix f eq x = let x' = f x in if eq x x' then x else fix f eq x'

(** {6 Application} *)

external (@@) : ('a -> 'b) -> 'a -> 'b = "%apply"
let apply = (@@)
let twice f x = f (f x)
(** [repeat f n x] applies [f] to [x] [n]-times *)
let rec repeat f n x = if n <= 0 then x else repeat f (n - 1) (f x)
(** [until p f x] repeatedly applies [f] to [x] until [p] holds *)
let rec until p f x = if p x then x else until p f (f x)
let feed x f = f x

(** {6 Composition} *)

let (<<<) f g = fun x -> f (g x)
let (>>) f g = fun x -> g (f x)
let comp f g = f <<< g
let comp2 f g1 g2 x1 x2 = f (g1 x1) (g2 x2)

(** {6 Reconnection} *)

let dup f x = f x x
(** argument flipping *)
let flip f x y = f y x
let side_effect f x = let () = f x in x
let sef = side_effect

(** {5 Currying} *)

let curry2 f x y = f (x, y)
let curry3 f x y z = f (x, y, z)
let curry4 f x y z w = f (x, y, z, w)
let curry_list1 f x xs = f (x :: xs)
let curry_list2 f x y xs = f (x :: y :: xs)
                             
(** {5 Uncurrying} *)

let uncurry2 f (x, y) = f x y
let uncurry3 f (x, y, z) = f x y z
let uncurry4 f (x, y, z, w) = f x y z w
let uncurry_list1 f (x :: xs) = f x xs
let uncurry_list2 f (x :: y :: xs) = f x y xs

(** {6 Pipelining} *)
      
let (<|) = (@@)
external (|>) : 'a -> ('a -> 'b) -> 'b = "%revapply"

(** {6 Branching} *)

let branch t f = fun b -> if b then t () else f ()
let if_ p t f = fun x -> if p x then t x else f x
let case pfs = fun x -> snd (List.find (fun (p, _) -> p x) pfs) x

(** {6 Sequencing} *)

let let_ f g = fun x -> g (f x) x

(** {6 Exception handling} *)

let try_ f g = fun x -> try f x with e -> g e x
let handle f g = try f () with exc -> g exc
let exc_fail f = fun x -> try f x with _ -> assert false

(** {6 Hooking} *)

let hook enabled before after main =
  if enabled then begin
    before ();
    let ret = main () in
    after ret;
    ret
  end else main ()
let pre before main = hook true before (const ()) main
let post after main = hook true id after main
