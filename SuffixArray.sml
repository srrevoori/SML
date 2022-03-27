(* Purely functional O(nlogn) Suffix Array Construction using Manber-Myers Algorithm *)
structure StringKey : ORD_KEY = 
  struct
    type ord_key = string
    val compare = String.compare
  end
structure RB = RedBlackMapFn(StringKey)
fun manberMyers s = let
  fun sortBucket bucket order res = let
    fun ins(d, s, i) = case RB.find (d, s) of 
        NONE => RB.insert (d, s, [i])
      | SOME x => RB.insert(d, s, i::x)
    val d = foldl (fn (i, h) => ins (h, String.substring(s, i, order) handle _ => String.extract(s, i, NONE) , i)) RB.empty bucket  
    in foldl (fn ([x], r) => x::r | (v, r) => sortBucket v (order * 2) r) res (RB.listItems d) end
  in List.rev (sortBucket (List.tabulate(String.size s, fn i => i)) 1 []) end
