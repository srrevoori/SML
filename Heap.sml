structure RandomizedHeap = (* 3 line Heap *)
  struct
    datatype 'a randheap = Null | Node of 'a * 'a randheap * 'a randheap

    fun meld ((Null, a) | (a, Null)) = a
      | meld (n1 as Node (x, l1, r1), n2 as Node(y, _, _)) = if x > y then meld (n2, n1) else if Random.flip () = 1 then Node(x, meld (l1, n2), r1) else Node(x, l1, meld (r1, n2))
  end
  
signature PQ =
sig
  structure Key : ORD_KEY
  type pq

  val empty : pq
  val isEmpty : pq -> bool

  val $ : Key.ord_key -> pq
  val fromList : Key.ord_key list -> pq
  val fromVector : Key.ord_key vector -> pq

  val size : pq -> int

  val insert : Key.ord_key * pq -> pq
  val findMin : pq -> Key.ord_key option
  val deleteMin : pq -> Key.ord_key option * pq
  val meld : pq * pq -> pq
  
  val iterate : ('a * Key.ord_key -> 'a) -> 'a -> pq -> 'a 
end

functor LeftistHeap (structure Key : ORD_KEY) :> PQ where type Key.ord_key = Key.ord_key =
struct
  structure Key = Key

  datatype pq = EMPTY | NODE of {rank : int, size : int, data : Key.ord_key, left : pq, right : pq}

  val empty = EMPTY

  fun isEmpty EMPTY = true
    | isEmpty _ = false

  fun rank EMPTY = 0
    | rank (NODE {rank, ...}) = rank

  fun size EMPTY = 0
    | size (NODE {size, ...}) = size

  fun mkNode (d, l, r) =
      if rank r < rank l
      then NODE {rank=1 + rank r, size=size l + size r + 1, data=d, left=l, right=r}
      else NODE {rank=1 + rank l, size=size l + size r + 1, data=d, left=r, right=l}

  fun $ kv = mkNode (kv, EMPTY, EMPTY)

  fun meld ((x, EMPTY) | (EMPTY, x)) = x
    | meld (n1 as NODE {data=d1, left=l1, right=r1, ...}, n2 as NODE {data=d2, left=l2, right=r2, ...}) =
      case Key.compare (d1, d2) of 
        LESS => mkNode (d1, l1, meld (r1, n2))
      | _ => mkNode (d2, l2, meld (n1, r2))

  fun insert (kv, Q) = meld ($ kv, Q)

  val fromList = List.foldl insert EMPTY
  
  fun fromVector V = reduce meld empty (Vector.map $ V)

  fun findMin EMPTY = NONE
    | findMin (NODE {data=kv, ...}) = SOME kv

  fun deleteMin EMPTY = (NONE, EMPTY)
    | deleteMin (NODE {data=kv, left=l, right=r, ...}) = (SOME kv, meld (l, r))
    
  fun iterate f b pq = 
    case deleteMin pq of
      (NONE, EMPTY) => b
    | (SOME kv, pq') => iterate f (f(b, kv)) pq'
end

functor BinaryHeap (structure E : ORDERED) :> PriorityQueue = 
  struct
    open DynamicArray
    structure Elem = E
    type Heap = Elem.T array * int
    exception EMPTY
    val p = Elem.leq
    val empty = (array(0, Elem.elem), 1)
    fun isEmpty (_, 1) = true
      | isEmpty _ = false
    fun findMin (_, 1) = raise EMPTY
      | findMin (H, n) = sub(H, 1)
    fun okAbove(H, i, j) = p(sub(H, j), sub(H, i))
    fun swapUp (H, i) = 
      let
        val parent = i div 2
        val temp = sub(H, i)
        val _ = update(H, i, sub(H, parent))
      in
        update(H, parent, temp)
      end
    fun insert (e, (H, n)) = 
      let 
        val _ = update(H, n, e)
        val i = ref n
      in
        while(!i > 1 andalso not (okAbove(H, (!i) div 2, !i))) do
          (swapUp(H, !i);
           i := !i div 2);
           (H, n + 1)
      end
    fun childSwap ((H, n), i) = 
      let
        val left = 2 * i
        val right = left + 1
      in
        if(right >= n orelse okAbove(H, left, right)) then 
          left 
        else 
          right
      end
    fun downSiftDone ((H, n), i) = 
      let
        val left = 2 * i
        val right = left + 1
      in
        okAbove(H, i, left) andalso (right >= n orelse okAbove(H, i, right))
      end
    fun siftDown (H, n) = 
      let
        val i = ref 1
      in
        while(2 * (!i) < n) do 
          if downSiftDone((H, n), !i) then i := n
          else
          (swapUp(H, childSwap((H, n), !i));
          i := childSwap((H, n), !i)); ()
      end
    fun deleteMin (H, n) = 
      let
        val m = n - 1
      in
        if m > 1 then
          ((update(H, 1, sub(H, m));
          siftDown(H, m)); (H, m))
        else (H, m)
      end
    fun merge ((H, n), (G, m)) = 
      if isEmpty(G, m) then (H, n) 
      else
        let
          val i = ref 1
        in
          while(!i < m) do 
            (insert(sub(G, !i), (H, n));
            i := !i + 1);
            (H, n)
        end
  end

