include "ActorTraces.i.dfy"

module ReductionModule
{
    import opened ActorTraces 

    /////////////////////////////////////////////////
    // Reduction trees
    /////////////////////////////////////////////////

    datatype Tree = Inner(reduced_entry:Entry, children:seq<Tree>, pivot_index:int) | Leaf(entry:Entry)

    function GetRootEntry(tree:Tree) : Entry
    {
        match tree
            case Inner(reduced_entry, children, pivot_index) => reduced_entry
            case Leaf(entry) => entry
    }

    function GetRootEntries(trees:seq<Tree>) : seq<Entry>
        ensures  var entries := GetRootEntries(trees);
                     |entries| == |trees|
                  && forall i {:trigger GetRootEntry(trees[i])}{:trigger GetRootEntries(trees)[i]} ::
                         0 <= i < |entries| ==> entries[i] == GetRootEntry(trees[i]);
    {
        if |trees| == 0 then [] else [GetRootEntry(trees[0])] + GetRootEntries(trees[1..])
    }

    predicate EntriesReducibleToEntry(entries:seq<Entry>, entry:Entry)
    {
        forall db:seq<SystemState> {:trigger SystemNextEntry(db[0], db[|entries|], entry)} ::
                |db| == |entries|+1
             && (forall i {:trigger SystemNextEntry(db[i], db[i+1], entries[i])} ::
                 0 <= i < |entries| ==> SystemNextEntry(db[i], db[i+1], entries[i]))
                 ==> SystemNextEntry(db[0], db[|entries|], entry)
    }

    predicate TreeChildrenReducibleToTreeRoot(tree:Tree)
    {
        tree.Inner? ==> EntriesReducibleToEntry(GetRootEntries(tree.children), GetRootEntry(tree))
    }

    predicate TreeRootPivotValid(tree:Tree)
    {
        tree.Inner? && |tree.children| > 0 ==>
               0 <= tree.pivot_index < |tree.children|
            && (forall i {:trigger EntryIsRightMover(GetRootEntry(tree.children[i]))} ::
                     0 <= i < tree.pivot_index ==> EntryIsRightMover(GetRootEntry(tree.children[i]))) 
            && (forall i {:trigger EntryIsLeftMover(GetRootEntry(tree.children[i]))} ::
                     tree.pivot_index < i < |tree.children| ==> EntryIsRightMover(GetRootEntry(tree.children[i])))
    }

    predicate TreeRootValid(tree:Tree)
    {
           TreeRootPivotValid(tree)
        && TreeChildrenReducibleToTreeRoot(tree)
    }

    predicate TreeValid(tree:Tree)
    {
           TreeRootValid(tree)
        && tree.Inner? ==> forall child {:trigger child in tree.children} :: child in tree.children ==> TreeRootValid(child)
    }
}
