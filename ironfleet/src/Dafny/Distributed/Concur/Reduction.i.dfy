include "ActorTraces.i.dfy"
include "SpecRefinement.i.dfy"

module ReductionModule
{
    import opened ActorTraces
    import opened SpecRefinementModule

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
        forall lb:seq<SystemState> {:trigger SystemNextEntry(lb[0], lb[|entries|], entry)} ::
                |lb| == |entries|+1
             && (forall i {:trigger SystemNextEntry(lb[i], lb[i+1], entries[i])} ::
                 0 <= i < |entries| ==> SystemNextEntry(lb[i], lb[i+1], entries[i]))
                 ==> SystemNextEntry(lb[0], lb[|entries|], entry)
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
                     tree.pivot_index < i < |tree.children| ==> EntryIsLeftMover(GetRootEntry(tree.children[i])))
    }

    predicate TreeRootValid(tree:Tree)
    {
           TreeRootPivotValid(tree)
        && TreeChildrenReducibleToTreeRoot(tree)
    }

    predicate TreeValid(tree:Tree)
    {
           TreeRootValid(tree)
        && (tree.Inner? ==> forall child {:trigger child in tree.children} :: child in tree.children ==> TreeValid(child))
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

    function GetLeafEntries(tree:Tree) : seq<Entry>
    {
        match tree
            case Leaf(e) => [e]
            case Inner(reduced_entry, children, pivot_index) => GetLeafEntriesForest(children)
    }
    
    function GetLeafEntriesForest(trees:seq<Tree>) : seq<Entry>
    {
        if |trees| == 0 then []
        else var head := GetLeafEntries(trees[0]);
             head + GetLeafEntriesForest(trees[1..])
    }
    
    function GetLeafEntriesPrefix(tree:Tree, designator:seq<int>) : seq<Entry>
        requires ValidTreeDesignator(designator, tree);
    {
        if |designator| == 0 then []
        else 
            assert tree.Inner?;
            GetLeafEntriesForestPrefix(tree.children, designator[0], designator[1..])
    }

    function GetLeafEntriesForestPrefix(trees:seq<Tree>, tree_index:int, designator:seq<int>) : seq<Entry>
        requires 0 <= tree_index < |trees|;
        requires ValidTreeDesignator(designator, trees[tree_index]);
    {
        if |trees| == 0 then 
            []
        else 
            GetLeafEntriesForest(trees[..tree_index]) + GetLeafEntriesPrefix(trees[tree_index], designator)
    }

    
    function GetLeafEntriesSuffix(tree:Tree, designator:seq<int>) : seq<Entry>
        requires ValidTreeDesignator(designator, tree);
    {
        if |designator| == 0 then []
        else 
            assert tree.Inner?;
            GetLeafEntriesForestSuffix(tree.children, designator[0], designator[1..])
    }

    function GetLeafEntriesForestSuffix(trees:seq<Tree>, tree_index:int, designator:seq<int>) : seq<Entry>
        requires 0 <= tree_index < |trees|;
        requires ValidTreeDesignator(designator, trees[tree_index]);
    {
        if |trees| == 0 then 
            []
        else 
            GetLeafEntriesSuffix(trees[tree_index], designator) + GetLeafEntriesForest(trees[tree_index+1..])
    }


    ghost method FindReducibleSubtree(tree:Tree) returns (success:bool, sub_tree:Tree, designator:seq<int>)
        requires TreeValid(tree);
        ensures success ==> ValidTreeDesignator(designator, tree)
                         && LookupTreeDesignator(designator, tree) == sub_tree
                         && TreeValid(sub_tree)
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
                    assert children[i] in tree.children;
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

    function ReduceTree(tree:Tree, designator:seq<int>) : Tree
        requires ValidTreeDesignator(designator, tree);
        requires var sub_tree := LookupTreeDesignator(designator, tree);
                 sub_tree.Inner? && (forall c :: c in sub_tree.children ==> c.Leaf?);
    {
        if |designator| == 0 then Leaf(tree.reduced_entry)
        else var child_index := designator[0];
             var child := tree.children[child_index];
             var sub_tree := ReduceTree(child, designator[1..]);
             Inner(tree.reduced_entry, tree.children[child_index := sub_tree], tree.pivot_index)
    }

    function ReduceTreeForest(trees:seq<Tree>, index:int, designator:seq<int>) : seq<Tree>
        requires 0 <= index < |trees|;
        requires ReduceTree.requires(trees[index], designator);
    {
        trees[index := ReduceTree(trees[index], designator)]
    }

    function CountInnerNodesForest(trees:seq<Tree>) : int
        ensures CountInnerNodesForest(trees) >= 0;
    {
        if |trees| == 0 then 0 else CountInnerNodes(trees[0]) + CountInnerNodesForest(trees[1..])
    }

    function CountInnerNodes(tree:Tree) : int
        ensures CountInnerNodes(tree) >= 0;
    {
        match tree {
            case Leaf(_) => 0
            case Inner(_, children, _) => 1 + CountInnerNodesForest(children)
        }
    }

    lemma lemma_CountInnerNodesForest(trees:seq<Tree>, index:int, new_tree:Tree)
        requires 0 <= index < |trees|;
        ensures  CountInnerNodesForest(trees[index := new_tree]) ==
                 CountInnerNodesForest(trees) - CountInnerNodes(trees[index]) + CountInnerNodes(new_tree);
    {
        if index == 0 {
        } else {
            lemma_CountInnerNodesForest(trees[1..], index-1, new_tree);
        }
    }

    lemma lemma_ReduceTreeDecreasesInnerNodes(tree:Tree, designator:seq<int>)
        requires ReduceTree.requires(tree, designator);
        ensures  CountInnerNodes(tree) > CountInnerNodes(ReduceTree(tree, designator));
    {
        if |designator| == 0 {
        } else {
            lemma_ReduceTreeDecreasesInnerNodes(tree.children[designator[0]], designator[1..]);
            lemma_CountInnerNodesForest(tree.children, designator[0], ReduceTree(tree.children[designator[0]], designator[1..]));
        }
    }

    lemma lemma_ReduceTreePreservesValidity(tree:Tree, designator:seq<int>)
        requires TreeValid(tree) && ReduceTree.requires(tree, designator)
        decreases |designator|;
        ensures  TreeValid(ReduceTree(tree, designator));
    {
        var reduced_tree := ReduceTree(tree, designator);
        if |designator| == 0 {
            assert TreeValid(reduced_tree);
        } else {
            var child_index := designator[0];
            var child := tree.children[child_index];
            var sub_tree := ReduceTree(child, designator[1..]);
            assert reduced_tree 
                == Inner(tree.reduced_entry, tree.children[child_index := sub_tree], tree.pivot_index);

            // OBSERVE: Various triggers for TreeRootPivotValid
            forall i | 0 <= i < reduced_tree.pivot_index
                ensures EntryIsRightMover(GetRootEntry(reduced_tree.children[i]));
            {
                if i != child_index {
                    assert reduced_tree.children[i] == tree.children[i];
                    assert EntryIsRightMover(GetRootEntry(reduced_tree.children[i]));
                } else {
                    assert GetRootEntry(reduced_tree.children[i]) 
                        == GetRootEntry(tree.children[i]);
                }
            }
            forall i | reduced_tree.pivot_index < i < |reduced_tree.children|
                ensures EntryIsLeftMover(GetRootEntry(reduced_tree.children[i]));
            {
                if i != child_index {
                    assert reduced_tree.children[i] == tree.children[i];
                    assert EntryIsLeftMover(GetRootEntry(reduced_tree.children[i]));
                } else {
                    assert GetRootEntry(reduced_tree.children[i]) 
                        == GetRootEntry(tree.children[i]);
                }
            }

            // OBSERVE: Re-establish EntriesReducibleToEntry
            var entry := reduced_tree.reduced_entry;
            var entries := GetRootEntries(reduced_tree.children);
            assert entries == GetRootEntries(tree.children);
            forall lb:seq<SystemState> {:trigger SystemNextEntry(lb[0], lb[|entries|], entry)} |
                    |lb| == |entries|+1
                 && (forall i {:trigger SystemNextEntry(lb[i], lb[i+1], entries[i])} ::
                     0 <= i < |entries| ==> SystemNextEntry(lb[i], lb[i+1], entries[i]))
                ensures SystemNextEntry(lb[0], lb[|entries|], entry);
            {
            }

            // OBSERVE: Re-establish children valid
            forall c | c in reduced_tree.children
                ensures TreeValid(c);
            {
                var i :| 0 <= i < |reduced_tree.children| && reduced_tree.children[i] == c;
                if i != child_index {
                    assert c in tree.children;  // OBSERVE
                } else {
                    assert c == sub_tree;
                    assert child in tree.children; // OBSERVE
                    lemma_ReduceTreePreservesValidity(child, designator[1..]);
                }
            }
            assert TreeValid(reduced_tree);
        }
    }

    lemma {:timeLimitMultiplier 2} lemma_ReduceTreeLeaves(tree:Tree, designator:seq<int>)
        requires ReduceTree.requires(tree, designator)
        decreases |designator|;
        ensures var old_leaves := GetLeafEntries(tree); 
                var reduced_tree := ReduceTree(tree, designator);
                var new_leaves := GetLeafEntries(reduced_tree); 
                var sub_tree := LookupTreeDesignator(designator, tree);
                var reduced_leaves := GetLeafEntries(sub_tree);
                var prefix := GetLeafEntriesPrefix(tree, designator);
                var suffix := GetLeafEntriesSuffix(tree, designator);
                old_leaves == prefix + reduced_leaves + suffix
             && new_leaves == prefix + [sub_tree.reduced_entry] + suffix;
    {
        var prefix := GetLeafEntriesPrefix(tree, designator);
        var suffix := GetLeafEntriesSuffix(tree, designator);

        var old_leaves := GetLeafEntries(tree); 
        var reduced_tree := ReduceTree(tree, designator);
        var new_leaves := GetLeafEntries(reduced_tree); 
        var sub_tree := LookupTreeDesignator(designator, tree);
        var reduced_leaves := GetLeafEntries(sub_tree);

        if tree.Leaf? {
            assert |designator| == 0;
        } else {
            assert ValidTreeDesignator(designator, tree);
            if |designator| == 0 {
                calc {
                    old_leaves;
                    GetLeafEntries(tree);
                    GetLeafEntries(sub_tree);
                    [] + GetLeafEntries(sub_tree) + [];
                    GetLeafEntriesPrefix(tree, designator) + GetLeafEntries(sub_tree) + GetLeafEntriesSuffix(tree, designator);
                    prefix + reduced_leaves + suffix;
                }
                calc {
                    new_leaves;
                    GetLeafEntries(reduced_tree);
                    GetLeafEntries(Leaf(tree.reduced_entry));
                    [tree.reduced_entry];
                    [sub_tree.reduced_entry];
                    [] + [sub_tree.reduced_entry] + [];
                    prefix + [sub_tree.reduced_entry] + suffix;
                }
            } else {
                assert |designator| > 0;
                assert tree.children[designator[0]] in tree.children;  // OBSERVE
                lemma_ReduceTreeLeaves(tree.children[designator[0]], designator[1..]); 
                calc {
                    old_leaves;
                    GetLeafEntries(tree);
                    GetLeafEntriesForest(tree.children);
                        { 
                            lemma_FunctionAdds(tree.children[..designator[0]+1], tree.children[designator[0]+1..],
                                               GetLeafEntriesForest, GetLeafEntries);
                            assert tree.children 
                                == tree.children[..designator[0]+1] + tree.children[designator[0]+1..];
                        }
                      GetLeafEntriesForest(tree.children[..designator[0]+1])
                    + GetLeafEntriesForest(tree.children[designator[0]+1..]);
                        { 
                            lemma_FunctionAdds(tree.children[..designator[0]], [tree.children[designator[0]]],
                                               GetLeafEntriesForest, GetLeafEntries);
                            assert tree.children[..designator[0]+1] 
                                == tree.children[..designator[0]] + [tree.children[designator[0]]];
                        }
                      GetLeafEntriesForest(tree.children[..designator[0]])
                    + GetLeafEntriesForest([tree.children[designator[0]]])
                    + GetLeafEntriesForest(tree.children[designator[0]+1..]);

                      GetLeafEntriesForest(tree.children[..designator[0]])
                    + GetLeafEntries(tree.children[designator[0]])
                    + GetLeafEntriesForest(tree.children[designator[0]+1..]);

                      GetLeafEntriesForest(tree.children[..designator[0]])
                    + GetLeafEntriesPrefix(tree.children[designator[0]], designator[1..])
                    + GetLeafEntries(sub_tree)
                    + GetLeafEntriesSuffix(tree.children[designator[0]], designator[1..])
                    + GetLeafEntriesForest(tree.children[designator[0]+1..]);
                    GetLeafEntriesPrefix(tree, designator) + GetLeafEntries(sub_tree) + GetLeafEntriesSuffix(tree, designator);
                    prefix + reduced_leaves + suffix;
                }

                var child_index := designator[0];
                var child := tree.children[child_index];
                var reduced_tree' := ReduceTree(child, designator[1..]);
                var new_children := tree.children[child_index := reduced_tree'];

                calc {
                    new_leaves;
                    GetLeafEntries(reduced_tree);
                    GetLeafEntries(Inner(tree.reduced_entry, new_children, tree.pivot_index));
                    GetLeafEntriesForest(new_children);
                        { 
                            lemma_FunctionAdds(new_children[..child_index], new_children[child_index..],
                                               GetLeafEntriesForest, GetLeafEntries);
                            assert new_children == new_children[..child_index] + new_children[child_index..];
                        }
                    GetLeafEntriesForest(new_children[..child_index]) + GetLeafEntriesForest(new_children[child_index..]);
                        { 
                            lemma_FunctionAdds([new_children[child_index]], new_children[child_index+1..],
                                               GetLeafEntriesForest, GetLeafEntries);
                            assert new_children[child_index..] == [new_children[child_index]] + new_children[child_index+1..];
                        }
                      GetLeafEntriesForest(new_children[..child_index]) 
                    + GetLeafEntriesForest([new_children[child_index]]) 
                    + GetLeafEntriesForest(new_children[child_index+1..]);

                      GetLeafEntriesForest(new_children[..child_index]) 
                    + GetLeafEntries(new_children[child_index]) 
                    + GetLeafEntriesForest(new_children[child_index+1..]);

                      GetLeafEntriesForest(new_children[..child_index]) 
                    + GetLeafEntries(reduced_tree') 
                    + GetLeafEntriesForest(new_children[child_index+1..]);
                        calc {
                            GetLeafEntries(reduced_tree'); 
                            GetLeafEntries(ReduceTree(child, designator[1..]));
                                // Induction hypothesis
                              GetLeafEntriesPrefix(child, designator[1..]) 
                            + [LookupTreeDesignator(designator[1..], child).reduced_entry] 
                            + GetLeafEntriesSuffix(child, designator[1..]);

                              GetLeafEntriesPrefix(child, designator[1..]) 
                            + [LookupTreeDesignator(designator, tree).reduced_entry] 
                            + GetLeafEntriesSuffix(child, designator[1..]);

                              GetLeafEntriesPrefix(child, designator[1..]) 
                            + [sub_tree.reduced_entry] 
                            + GetLeafEntriesSuffix(child, designator[1..]);
                        }

                      GetLeafEntriesForest(new_children[..child_index])
                    + GetLeafEntriesPrefix(child, designator[1..])
                    + [sub_tree.reduced_entry]
                    + GetLeafEntriesSuffix(child, designator[1..])
                    + GetLeafEntriesForest(new_children[child_index+1..]);
                        { assert tree.children[..child_index] == new_children[..child_index];
                          assert tree.children[child_index+1..] == new_children[child_index+1..]; }
                      GetLeafEntriesForest(tree.children[..child_index])
                    + GetLeafEntriesPrefix(tree.children[child_index], designator[1..])
                    + [sub_tree.reduced_entry]
                    + GetLeafEntriesSuffix(tree.children[child_index], designator[1..])
                    + GetLeafEntriesForest(tree.children[child_index+1..]);

                    GetLeafEntriesPrefix(tree, designator) + [sub_tree.reduced_entry] + GetLeafEntriesSuffix(tree, designator);
                    prefix + [sub_tree.reduced_entry] + suffix;
                }
            }
        }
    }


    lemma {:timeLimitMultiplier 3} lemma_ReduceTreeLeavesForestOld(trees:seq<Tree>, index:int, designator:seq<int>)
        requires 0 <= index < |trees|;
        requires ReduceTree.requires(trees[index], designator)
        decreases |designator|;
        ensures var tree := trees[index];
                var old_leaves := GetLeafEntriesForest(trees); 
                var reduced_trees := ReduceTreeForest(trees, index, designator);
                var sub_tree := LookupTreeDesignator(designator, tree);
                var reduced_leaves := GetLeafEntries(sub_tree);
                var prefix := GetLeafEntriesForestPrefix(trees, index, designator);
                var suffix := GetLeafEntriesForestSuffix(trees, index, designator);
                old_leaves == prefix + reduced_leaves + suffix;
    {
        var tree := trees[index];
        var old_leaves := GetLeafEntriesForest(trees); 
        var reduced_trees := ReduceTreeForest(trees, index, designator);
        var sub_tree := LookupTreeDesignator(designator, tree);
        var reduced_leaves := GetLeafEntries(sub_tree);
        var prefix := GetLeafEntriesForestPrefix(trees, index, designator);
        var suffix := GetLeafEntriesForestSuffix(trees, index, designator);

        calc {
            old_leaves;
            GetLeafEntriesForest(trees); 
                { 
                    lemma_FunctionAdds(trees[..index], trees[index..],
                                       GetLeafEntriesForest, GetLeafEntries);
                    assert trees == trees[..index] + trees[index..];
                }
            GetLeafEntriesForest(trees[..index]) + GetLeafEntriesForest(trees[index..]); 
                { 
                    lemma_FunctionAdds([trees[index]], trees[index+1..],
                                       GetLeafEntriesForest, GetLeafEntries);
                    assert trees[index..] == [trees[index]] + trees[index+1..];
                }
            GetLeafEntriesForest(trees[..index]) + GetLeafEntriesForest([trees[index]]) + GetLeafEntriesForest(trees[index+1..]); 
            GetLeafEntriesForest(trees[..index]) + GetLeafEntries(trees[index]) + GetLeafEntriesForest(trees[index+1..]); 
                { lemma_ReduceTreeLeaves(tree, designator); }
              GetLeafEntriesForestPrefix(trees, index, designator) 
            + reduced_leaves 
            + GetLeafEntriesForestSuffix(trees, index, designator);
            prefix + reduced_leaves + suffix;
        }
        
    }    
    
    lemma {:timeLimitMultiplier 4} lemma_ReduceTreeLeavesForestNew(trees:seq<Tree>, index:int, designator:seq<int>)
        requires 0 <= index < |trees|;
        requires ReduceTree.requires(trees[index], designator)
        decreases |designator|;
        ensures var tree := trees[index];
                var reduced_trees := ReduceTreeForest(trees, index, designator);
                var new_leaves := GetLeafEntriesForest(reduced_trees); 
                var sub_tree := LookupTreeDesignator(designator, tree);
                var reduced_leaves := GetLeafEntries(sub_tree);
                var prefix := GetLeafEntriesForestPrefix(trees, index, designator);
                var suffix := GetLeafEntriesForestSuffix(trees, index, designator);
                new_leaves == prefix + [sub_tree.reduced_entry] + suffix;
    {
        var tree := trees[index];
        var reduced_trees := ReduceTreeForest(trees, index, designator);
        var new_leaves := GetLeafEntriesForest(reduced_trees); 
        var sub_tree := LookupTreeDesignator(designator, tree);
        var reduced_leaves := GetLeafEntries(sub_tree);
        var prefix := GetLeafEntriesForestPrefix(trees, index, designator);
        var suffix := GetLeafEntriesForestSuffix(trees, index, designator);

        calc {
            new_leaves;
            GetLeafEntriesForest(reduced_trees); 
                { 
                    lemma_FunctionAdds(reduced_trees[..index], reduced_trees[index..],
                                       GetLeafEntriesForest, GetLeafEntries);
                    assert reduced_trees == reduced_trees[..index] + reduced_trees[index..];
                }
            GetLeafEntriesForest(reduced_trees[..index]) + GetLeafEntriesForest(reduced_trees[index..]); 
                { 
                    lemma_FunctionAdds([reduced_trees[index]], reduced_trees[index+1..],
                                       GetLeafEntriesForest, GetLeafEntries);
                    assert reduced_trees[index..] == [reduced_trees[index]] + reduced_trees[index+1..];
                    assert GetLeafEntriesForest(reduced_trees[index..])
                        == GetLeafEntriesForest([reduced_trees[index]]) + GetLeafEntriesForest(reduced_trees[index+1..]); 
                }
              GetLeafEntriesForest(reduced_trees[..index]) 
            + GetLeafEntriesForest([reduced_trees[index]]) 
            + GetLeafEntriesForest(reduced_trees[index+1..]); 
                { assert reduced_trees[..index] == trees[..index];
                  assert reduced_trees[index+1..] == trees[index+1..]; }
              GetLeafEntriesForest(trees[..index]) 
            + GetLeafEntries(reduced_trees[index]) 
            + GetLeafEntriesForest(trees[index+1..]); 
                { lemma_ReduceTreeLeaves(tree, designator); }
              GetLeafEntriesForest(trees[..index]) 
            + GetLeafEntriesPrefix(trees[index], designator)
            + [sub_tree.reduced_entry] 
            + GetLeafEntriesSuffix(trees[index], designator) 
            + GetLeafEntriesForest(trees[index+1..]);

              GetLeafEntriesForestPrefix(trees, index, designator) 
            + [sub_tree.reduced_entry] 
            + GetLeafEntriesForestSuffix(trees, index, designator);
            prefix + [sub_tree.reduced_entry] + suffix;
        }
        
    }

    lemma lemma_ReduceTreeLeavesForest(trees:seq<Tree>, index:int, designator:seq<int>)
        requires 0 <= index < |trees|;
        requires ReduceTree.requires(trees[index], designator)
        decreases |designator|;
        ensures var tree := trees[index];
                var old_leaves := GetLeafEntriesForest(trees); 
                var reduced_trees := ReduceTreeForest(trees, index, designator);
                var new_leaves := GetLeafEntriesForest(reduced_trees); 
                var sub_tree := LookupTreeDesignator(designator, tree);
                var reduced_leaves := GetLeafEntries(sub_tree);
                var prefix := GetLeafEntriesForestPrefix(trees, index, designator);
                var suffix := GetLeafEntriesForestSuffix(trees, index, designator);
                old_leaves == prefix + reduced_leaves + suffix
             && new_leaves == prefix + [sub_tree.reduced_entry] + suffix;
    {
        lemma_ReduceTreeLeavesForestOld(trees, index, designator);
        lemma_ReduceTreeLeavesForestNew(trees, index, designator);
    }
}
