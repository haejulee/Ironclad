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

    predicate ValidTreeDesignator(designator:seq<int>, tree:Tree) 
    {
        |designator| > 0 ==>
        var child_index := designator[0];
            tree.Inner? && 0 <= child_index < |tree.children| 
         && ValidTreeDesignator(designator[1..], tree.children[child_index])
    }

    function LookupTreeDesignator(designator:seq<int>, tree:Tree) : Tree
        requires ValidTreeDesignator(designator, tree);
    {
        if |designator| == 0 then tree
        else LookupTreeDesignator(designator[1..], tree.children[designator[0]])
    }

    function GetEntries(trees:seq<Tree>) : seq<Entry>
    {
        if |trees| == 0 then []
        else var head := (match trees[0]
                            case Leaf(e) => [e]
                            case Inner(reduced_entry, children, pivot_index) => GetEntries(children)
                         );
             head + GetEntries(trees[1..])
    }

    ghost method FindReducibleSubtree(tree:Tree) returns (success:bool, sub_tree:Tree, designator:seq<int>)
        ensures success ==> ValidTreeDesignator(designator, tree)
                         && LookupTreeDesignator(designator, tree) == sub_tree
                         && sub_tree.Inner?
                         && (forall c :: c in sub_tree.children ==> c.Leaf?);
        ensures !success ==> tree.Leaf?;
    {
        match tree {
            case Leaf(_) => success := false;
            case Inner(reduced_entry, children, pivot_index) =>
                var i := 0;
                while i < |children| 
                    invariant 0 <= i <= |children|;
                    invariant forall j :: 0 <= j < i ==> children[j].Leaf?;
                {
                    success, sub_tree, designator := FindReducibleSubtree(children[i]);
                    if success {
                        designator := [i] + designator;
                        return;
                    }
                    i := i + 1;
                }
                success := true;
                sub_tree := tree;
                designator := [];
        }
    }
}
