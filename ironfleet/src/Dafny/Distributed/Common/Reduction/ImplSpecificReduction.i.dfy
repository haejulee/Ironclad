include "../Framework/Host.s.dfy"
include "../Framework/AbstractService.s.dfy"
include "ExtendedTrace.i.dfy"

abstract module ImplSpecificReductionModule {

    import opened HostModule
    import opened AbstractServiceModule
    import opened ExtendedTraceModule

    predicate ExtendedEntryIsRightMover(entry:ExtendedEntry)
    predicate ExtendedEntryIsLeftMover(entry:ExtendedEntry)

    lemma lemma_MoverCommutativityForExtendedEntries(
        entry1:ExtendedEntry,
        entry2:ExtendedEntry,
        ls1:ExtendedSystemState,
        ls2:ExtendedSystemState,
        ls3:ExtendedSystemState
        )
        returns
        (ls2':ExtendedSystemState)
        requires entry1.actor != entry2.actor;
        requires ExtendedSystemNextEntry(ls1, ls2, entry1);
        requires ExtendedSystemNextEntry(ls2, ls3, entry2);
        requires ExtendedEntryIsRightMover(entry1) || ExtendedEntryIsLeftMover(entry2);
        ensures  ExtendedSystemNextEntry(ls1, ls2', entry2);
        ensures  ExtendedSystemNextEntry(ls2', ls3, entry1);

    lemma lemma_RightMoverForwardPreservation(rightMover:ExtendedEntry, ls:ExtendedSystemState, ls':ExtendedSystemState, hs:SpecState)
        requires ExtendedEntryIsRightMover(rightMover);
        requires ExtendedSystemNextEntry(ls, ls', rightMover);
        requires SpecCorrespondence(ls.ss, hs);
        ensures  SpecCorrespondence(ls'.ss, hs);

    lemma lemma_LeftMoverBackwardPreservation(leftMover:ExtendedEntry, ls:ExtendedSystemState, ls':ExtendedSystemState, hs:SpecState)
        requires ExtendedEntryIsLeftMover(leftMover);
        requires ExtendedSystemNextEntry(ls, ls', leftMover);
        requires SpecCorrespondence(ls'.ss, hs);
        ensures  SpecCorrespondence(ls.ss, hs);

    predicate IsValidHostBehavior(config:ConcreteConfiguration, actor:Actor, hb:seq<AbstractHostState>, ios_seq:seq<seq<Event>>)
    {
           |hb| == |ios_seq| + 1
        && HostInit(hb[0], config, actor)
        && (forall i :: 0 <= i < |ios_seq| ==> HostNext(hb[i], hb[i+1], ios_seq[i]))
    }
        
    predicate SetupForLeftMoversAlwaysEnabled(
        actor:Actor,
        ios:seq<Event>,
        pivot_index:int,
        left_mover_pos:int,
        other_actor_entries:seq<ExtendedEntry>,
        lb:seq<ExtendedSystemState>
        )
    {
           0 <= pivot_index < left_mover_pos < |ios|
        && |lb| == left_mover_pos + |other_actor_entries| + 1
        && (forall other_entry :: other_entry in other_actor_entries ==> other_entry.actor != actor)
        && (forall i :: 0 <= i < left_mover_pos ==> ExtendedSystemNextEntry(lb[i], lb[i+1], Entry(actor, ExtendedActionEvent(ios[i]))))
        && (forall i :: 0 <= i < |other_actor_entries| ==> ExtendedSystemNextEntry(lb[left_mover_pos+i], lb[left_mover_pos+i+1], other_actor_entries[i]))
    }

    lemma lemma_HostNextCompatibleWithReduction(
        config:ConcreteConfiguration,
        actor:Actor,
        s:AbstractHostState,
        s':AbstractHostState,
        ios:seq<Event>
        ) returns (
        pivot_index:int
        )
        requires exists hb, ios_seq :: IsValidHostBehavior(config, actor, hb, ios_seq) && last(hb) == s;
        requires HostNext(s, s', ios);
        ensures  0 <= pivot_index <= |ios|;
        ensures  forall i :: 0 <= i < pivot_index ==> ExtendedEntryIsRightMover(Entry(actor, ExtendedActionEvent(ios[i])));
        ensures  forall i :: pivot_index < i < |ios| ==> ExtendedEntryIsLeftMover(Entry(actor, ExtendedActionEvent(ios[i])));
        ensures  forall b:seq<ExtendedSystemState> {:trigger ExtendedSystemNextEntry(b[0], b[|ios|], Entry(actor, ExtendedActionPerformIos(ios)))} ::
                     |b| == |ios| + 1
                  && (forall i {:trigger ExtendedSystemNextEntry(b[i], b[i+1], Entry(actor, ExtendedActionEvent(ios[i])))} ::
                        0 <= i < |ios| ==> ExtendedSystemNextEntry(b[i], b[i+1], Entry(actor, ExtendedActionEvent(ios[i]))))
                  ==> ExtendedSystemNextEntry(b[0], b[|ios|], Entry(actor, ExtendedActionPerformIos(ios)));
        ensures  forall left_mover_pos:int, other_actor_entries:seq<ExtendedEntry>, lb:seq<ExtendedSystemState>
                     {:trigger SetupForLeftMoversAlwaysEnabled(actor, ios, pivot_index, left_mover_pos, other_actor_entries, lb)} ::
                         SetupForLeftMoversAlwaysEnabled(actor, ios, pivot_index, left_mover_pos, other_actor_entries, lb)
                     ==> exists ls' :: ExtendedSystemNextEntry(last(lb), ls', Entry(actor, ExtendedActionEvent(ios[left_mover_pos])));
        
    lemma lemma_AtomicRefinement(
        config:ConcreteConfiguration,
        trace:ExtendedTrace,
        eb:seq<ExtendedSystemState>
        )
        requires ConcreteConfigurationInvariants(config);
        requires IsValidExtendedSystemTraceAndBehavior(config, trace, eb);
        requires forall actor :: actor in TrackedActorsInConfig(config) ==> actor in eb[0].states;
        requires forall entry :: entry in trace ==> IsValidActor(entry.actor);
        requires forall entry :: entry in trace ==> if entry.actor in TrackedActorsInConfig(config) then entry.action.ExtendedActionHostNext?
                                              else IsRealExtendedAction(entry.action);
        ensures  BehaviorRefinesSpec(eb, GetSpec(config), GetExtendedSystemSpecRefinementRelation());

}
