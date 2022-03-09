functor SegTree(val n : int) = (* 3 line segtree with mutation *)
struct 
    val T = Array.tabulate (2 * n, fn _ => 0) 
    fun update i x = (Array.update (T, i + n, x); Y (fn u => fn i => if i = 0 then () else (Array.update (T, i, Array.sub (T, 2 * i) + Array.sub (T, 2 * i + 1)); u (i div 2))) ((i + n) div 2))
    fun query l r = Y (fn f => fn (v, l, r, i, j) => if l = i andalso r = j then Array.sub (T, v) else let val m = (l + r) div 2 in (if i <= m then f (2 * v, l, m, i, Int.min (m, j)) else 0) + (if j > m then f (2 * v + 1, m + 1, r, Int.max (i, m + 1), j) else 0) end) (1, 0, n - 1, l, r)
end 

signature SEGTREE = 
  sig
    type segtree
    structure Key : MONOID
    
    val make : int -> segtree
    val update : segtree -> int -> Key.t -> segtree
    val query : segtree -> int -> int -> Key.t
  end

functor SegTree(structure Key : MONOID) :> SEGTREE where type Key.t = Key.t = (* Purely Functional *)
  struct
    structure Key = Key
    
    datatype segtree = Nil | Node of int * int * Key.t * segtree * segtree
    
    fun make n =
      let fun sub l r =
            if r = l + 1
            then Node (l, r, Key.I, Nil, Nil)
            else let val m = (l + r) div 2 in Node (l, r, Key.I, sub l m, sub m r) end
      in sub 0 (n * 2) end
      
    fun value_of Nil = raise Fail "val"
      | value_of (Node (_, _, v, _, _)) = v
      
    fun update Nil p v = raise Fail "upd"
      | update (Node (l, r, _, Nil, rs)) p v = Node (l, r, v, Nil, rs)
      | update (Node (l, r, _, ls, rs)) p v = 
        let
          val m = (l + r) div 2 
          val (ls, rs) = if p < m then (update ls p v, rs) else (ls, update rs p v)
        in 
          Node (l, r, Key.f (value_of ls, value_of rs), ls, rs)
        end
      
    fun query Nil lpos rpos = raise Fail "query"
      | query (Node (l, r, v, ls, rs)) lpos rpos =
           if r <= lpos orelse rpos <= l then Key.I
           else if lpos <= l andalso r <= rpos then v
           else Key.f (query ls lpos rpos, query rs lpos rpos) 
  end
