(* Implicit Treap - solves reverse on segment problem*)


datatype treap = Empty | Node of real * int * int * bool * treap * treap

fun key Empty = 0
  | key (Node (_, k, _, _, _, _)) = k

fun update Empty = Empty
  | update (Node (p, _, v, f, l, r)) = Node (p, 1 + key l + key r, v, f, l, r) 

fun flip Empty = Empty
  | flip (Node (p, k, v, f, l, r)) = Node (p, k, v, not f, l, r)

fun push (Node (p, k, v, true, l, r)) = Node (p, k, v, false, flip r, flip l)
  | push t = t

fun join (l, r) = 
  let
    val (l', r') = (push l, push r)
  in
    case (l', r') of
      (Empty, _) => r'
    | (_, Empty) => l'
    | (Node (p1, c1, v1, f1, l1, r1), Node (p2, c2, v2, f2, l2, r2)) => if p1 > p2 then update (Node (p1, c1, v1, f1, l1, join (r1, r'))) else update (Node (p2, c2, v2, f2, join (l', l2), r2))
  end

fun split (Empty, _, _) = (Empty, Empty)
  | split (t, k, add) = 
    let
      val (t' as Node (p, k', v, f, l, r)) = push t
    in
      if k <= add + key l then
        let val (l', r') = split (l, k, add) in (l', update (Node (p, k', v, f, r', r))) end
      else 
        let val (l', r') = split(r, k, add + 1 + key l) in (update (Node (p, k', v, f, l, l')), r') end
    end
    
fun reverse (t, l, r) = 
  let
    val (t1, t2) = split (t, l, 0)
    val (t2, t3) = split (t2, r - l + 1, 0)
  in
    join(join (t1, flip t2), t3)
  end
  
(* Augmented Treap adapted from 15-210 *) 

signature MONOID =
sig
  type t
  val I : t
  val f : t * t -> t
end
signature ORDKEY =
sig
  type t
  val compare : t * t -> order
end

signature TREAP =
sig
  structure Key : ORDKEY
  structure Val : MONOID

  type bst

  val size : bst -> int
  val reduceVal : bst -> Val.t

  val empty : unit -> bst

  val join : bst * bst -> bst
  val joinMid : bst * (Key.t * Val.t) * bst -> bst

  val split : bst * Key.t -> bst * Val.t option * bst
    
  val insert : bst * (Key.t * Val.t) -> bst 
  val delete : bst * Key.t -> bst
  val find : bst * Key.t -> Val.t option

  val $ : Key.t * Val.t -> bst
  val fromList : (Key.t * Val.t) list -> bst 
  
  val getRange : bst -> Key.t * Key.t -> bst
  
  val min : bst -> Key.t option
  val max : bst -> Key.t option

  val union : bst * bst -> bst
  val intersection : bst * bst -> bst
  val difference : bst * bst -> bst

  val rank : bst * Key.t -> int
  val select : bst * int -> Key.t option
  val splitRank : bst * int -> bst * bst
end

functor Treap
  (structure Key : ORDKEY
   structure Val : MONOID)
  :> TREAP where type Key.t = Key.t and type Val.t = Val.t =
struct
  structure Key = Key
  structure Val = Val

  datatype bst =
    Empty
  | Node of { data : { key : Key.t
                     , rvalue : Val.t
                     , pri : real }
            , size : int
            , reduced : Val.t
            , left : bst
            , right : bst }

  fun reduceVal Empty = Val.I
    | reduceVal (Node {reduced, ...}) = reduced

  fun size Empty = 0
    | size (Node {size, ...}) = size

  fun makeNode (l, data, r) =
    Node { data = data
         , size = size l + 1 + size r
         , reduced = Val.f (reduceVal l, Val.f (#rvalue data, reduceVal r))
         , left = l
         , right = r }

  fun empty () = Empty

  fun $ (k, rv) = makeNode (Empty, {key = k, rvalue = rv, pri = Random.randReal (0.0, 1.0)}, Empty)

  fun max Empty = NONE
    | max (Node {data={key, ...}, right, ...}) =
      case right of Empty => SOME key | _ => max right
  fun min Empty = NONE
    | min (Node {data={key, ...}, left, ...}) =
      case left of Empty => SOME key | _ => min left
       
  fun join (Empty, t2) = t2
    | join (t1, Empty) = t1
    | join (t1 as Node {data=data1, left=l1, right=r1, ...}, t2 as Node {data=data2, left=l2, right=r2, ...}) =
      if #pri data1 > #pri data2 then makeNode (l1, data1, join (r1, t2))
      else makeNode (join (t1, l2), data2, r2)

  fun split (Empty, k) = (Empty, NONE, Empty)
    | split (Node {data, left, right, ...}, k) =
      case Key.compare (k, #key data) of
        LESS =>
          let val (leftl, b, leftr) = split (left, k)
          in (leftl, b, makeNode (leftr, data, right)) end
      | EQUAL => (left, SOME (#rvalue data), right)
      | GREATER =>
          let val (rightl, b, rightr) = split (right, k)
          in (makeNode (left, data, rightl), b, rightr) end
            
  fun joinMid (t1, (k, v), t2) = join (t1, join ($ (k, v), t2))

  fun insert (t, (k, v)) = let val (L, _, R) = split (t, k) in joinMid (L, (k, v), R) end 
  
  fun delete (t, k) = let val (L, _, R) = split (t, k) in join (L, R) end 

  val find = #2 o split

  val fromList = foldl (fn (kv, t) => insert(t, kv)) (empty())
  
  fun getRange T (lo, hi) = 
    let
      val (_, x, R) = split (T, lo)
      val geq = case x of NONE => R | SOME y => insert (R, (lo, y))
      val (L, x, _) = split (geq, hi)
    in
      case x of NONE => L | SOME y => insert (L, (hi, y))
    end

  fun union (Empty, T2) = T2
    | union (T1, Empty) = T1
    | union (Node {data, left, right, ...}, T2) = 
      let 
        val (k, v) = (#key data, #rvalue data)
        val (L2, _, R2) = split (T2, k)
        val (L, R) = (union(left, L2), union(right, R2))
      in
        joinMid(L, (k, v), R)
      end 

  fun intersection (Empty, T2) = Empty
    | intersection (T1, Empty) = Empty
    | intersection (Node {data, left, right, ...}, T2) = 
      let 
        val (k, v) = (#key data, #rvalue data)
        val (L2, a, R2) = split (T2, k)
        val (L, R) = (intersection(left, L2), intersection(right, R2))
      in
        if isSome a then joinMid(L, (k, v), R) else join(L, R)
      end   
  
  fun difference (Empty, T2) = Empty
    | difference (T1, Empty) = T1
    | difference (Node {data, left, right, ...}, T2) = 
      let 
        val (k, v) = (#key data, #rvalue data)
        val (L2, a, R2) = split (T2, k)
        val (L, R) = (difference(left, L2), difference(right, R2))
      in
        if isSome a then join(L, R) else joinMid(L, (k, v), R)
      end   
  
  val rank = size o #1 o split 

  fun select (Empty, i) = NONE
    | select (Node {data, left, right, ...}, i) = 
      case Int.compare(1 + size left, i) of
        EQUAL => SOME (#key data)
      | LESS => select (right, (i - (size left) - 1))
      | GREATER => select (left, i)
  
  fun splitRank (t, i) = 
    case select (t, i) of
      NONE => raise Fail "invariant"
    | SOME k =>
        let val (l, _, r) = split (t, k)
        in (l, insert (r, (k, valOf (find (t, k)))))
        end
end
