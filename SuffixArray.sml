(* Purely functional O(nlogn) Suffix Array Construction using a modified Manber-Myers Algorithm *)
structure StringKey : ORD_KEY = 
  struct
    type ord_key = string
    val compare = String.compare
  end
structure RB = RedBlackMapFn(StringKey)
fun suffixArray s = let
  fun sort b l A = let
    fun ins(d, s, i) = RB.insert(d, s, i::(RB.lookup(d, s) handle _ => []))
    val d = foldl (fn (i, h) => ins (h, String.substring(s, i, l) handle _ => String.extract(s, i, NONE) , i)) RB.empty b  
    in foldl (fn ([x], r) => x::r | (v, r) => sort v (l * 2) r) A (RB.listItems d) end
  in List.rev (sort (List.tabulate(String.size s, fn i => i)) 1 []) end
