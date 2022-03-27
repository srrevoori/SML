(* Purely functional O(nlogn) Suffix Array Construction using Manber-Myers Algorithm *)

structure StringKey : ORD_KEY = 
  struct
    type ord_key = string
    val compare = String.compare
  end
structure RB = RedBlackMapFn(StringKey)
fun suffixArray s = 
  let
    fun sortBucket bucket order res = 
      let
        fun ins(d, s, i) = case RB.find (d, s) of 
            NONE => RB.insert (d, s, [i])
          | SOME x => RB.insert(d, s, i::x)
        val d = foldl (fn (i, h) => ins (h, String.substring(s, i, order) handle _ => String.extract(s, i, NONE) , i)) RB.empty bucket  
        val l = RB.listItemsi d
      in
        foldl (fn ((k, v), r) => if List.length v > 1 then sortBucket v (order * 2) r else List.hd v::r) res l
      end
  in
    List.rev (sortBucket (List.tabulate(String.size s, fn i => i)) 1 [])
  end
