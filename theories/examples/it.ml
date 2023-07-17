type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

type error =
| RuntimeErr
| OtherError

module type opsInterp = sig
  type 'a ins
  type 'b outs
  val fmap_ins : ('a -> 'b) -> 'a ins -> 'b ins
  val fmap_outs : ('a -> 'b) -> 'a outs -> 'b outs
end

module ITrees (E : opsInterp) = struct
  type it =
    | Err : error -> it
    | Nat : int -> it
    | Fun : (it -> it) -> it
    | Tau : it -> it
    | Vis : it E.ins * (it E.outs -> it) -> it

  let vis x k = Vis (x,k)

  let rec it_rec1 : (error -> 'a) ->
                    (int -> 'a) -> 
                    (((it, 'a) sum -> it * 'a) -> 'a) ->
                    (it * 'a -> 'a) ->
                    ((it * 'a) E.ins -> ((it, 'a) sum E.outs -> it * 'a) -> 'a) ->
                    it -> 'a = fun perr pnat parr ptau pvis t ->
    match t with
    | Err e -> perr e
    | Nat x -> pnat x
    | Fun f -> parr (fun y ->
                   match y with
                   | Inl t -> let r = f t in
                              (r, it_rec1 perr pnat parr ptau pvis r)
                   | Inr v -> let r = f (it_rec2 v) in
                              (r, it_rec1 perr pnat parr ptau pvis r))
    | Tau t -> ptau (t, it_rec1 perr pnat parr ptau pvis t)
    | Vis (x,k) ->
       let x' = E.fmap_ins (fun x -> (x, it_rec1 perr pnat parr ptau pvis x)) x in
       let s_outs = E.fmap_outs (function
                        | Inl t -> t
                        | Inr v -> it_rec2 v)
       in
       let k' x = let r = k (s_outs x) in  (r, it_rec1 perr pnat parr ptau pvis r)
       in
       pvis x' k'
  and it_rec2 : 'a -> it = fun x -> Nat(1)
end
