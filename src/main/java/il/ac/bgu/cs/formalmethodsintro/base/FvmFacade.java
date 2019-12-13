package il.ac.bgu.cs.formalmethodsintro.base;

import java.io.InputStream;
import java.util.*;

import il.ac.bgu.cs.formalmethodsintro.base.automata.Automaton;
import il.ac.bgu.cs.formalmethodsintro.base.automata.MultiColorAutomaton;
import il.ac.bgu.cs.formalmethodsintro.base.channelsystem.ChannelSystem;
import il.ac.bgu.cs.formalmethodsintro.base.circuits.Circuit;
import il.ac.bgu.cs.formalmethodsintro.base.exceptions.StateNotFoundException;
import il.ac.bgu.cs.formalmethodsintro.base.ltl.LTL;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.ActionDef;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.ConditionDef;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.PGTransition;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.ProgramGraph;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.AlternatingSequence;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TSTransition;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.formalmethodsintro.base.util.Pair;
import il.ac.bgu.cs.formalmethodsintro.base.verification.VerificationResult;

/**
 * Interface for the entry point class to the HW in this class. Our
 * client/testing code interfaces with the student solutions through this
 * interface only. <br>
 * More about facade: {@linkplainhttp://www.vincehuston.org/dp/facade.html}.
 */
public class FvmFacade {

    private static FvmFacade INSTANCE = null;

    /**
     * @return an instance of this class.
     */
    public static FvmFacade get() {
        if (INSTANCE == null) {
            INSTANCE = new FvmFacade();
        }
        return INSTANCE;
    }

    /**
     * Checks whether a transition system is action deterministic. I.e., if for
     * any given p and α there exists only a single tuple (p,α,q) in →. Note
     * that this must be true even for non-reachable states.
     *
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param <P> Type of atomic propositions.
     * @param ts  The transition system being tested.
     * @return {@code true} iff the action is deterministic.
     */
    public <S, A, P> boolean isActionDeterministic(TransitionSystem<S, A, P> ts) {
        for (S state : ts.getStates())
            for (A alpha : ts.getActions()) {
                if (post(ts, state, alpha).size() > 1)
                    return false;
            }
        return ts.getInitialStates().size() <= 1;
    }


    /**
     * Checks whether an action is ap-deterministic (as defined in class), in
     * the context of a given {@link TransitionSystem}.
     *
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param <P> Type of atomic propositions.
     * @param ts  The transition system being tested.
     * @return {@code true} iff the action is ap-deterministic.
     */
    public <S, A, P> boolean isAPDeterministic(TransitionSystem<S, A, P> ts) {
        for (Set<P> set : powerSet(ts.getAtomicPropositions())) { // for A in AP
            Set<S> s_followers = new HashSet<>();
            for (S state : ts.getStates()) {  // for s in S
                if (ts.getLabelingFunction().get(state).equals(set))
                    s_followers.add(state);
            }
            for (S state : ts.getStates()) {
                Set<S> intersection = new HashSet<S>(post(ts, state));
                intersection.retainAll(s_followers);
                if (intersection.size() > 1)
                    return false;
            }
        }
        return ts.getInitialStates().size() <= 1;
    }

    /**
     * Checks whether an alternating sequence is an execution of a
     * {@link TransitionSystem}, as defined in class.
     *
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param <P> Type of atomic propositions.
     * @param ts  The transition system being tested.
     * @param e   The sequence that may or may not be an execution of {@code ts}.
     * @return {@code true} iff {@code e} is an execution of {@code ts}.
     */
    public <S, A, P> boolean isExecution(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        return isExecutionFragment(ts, e) && isInitialExecutionFragment(ts, e) && isMaximalExecutionFragment(ts, e);
    }

    /**
     * Checks whether an alternating sequence is an execution fragment of a
     * {@link TransitionSystem}, as defined in class.
     *
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param <P> Type of atomic propositions.
     * @param ts  The transition system being tested.
     * @param e   The sequence that may or may not be an execution fragment of
     *            {@code ts}.
     * @return {@code true} iff {@code e} is an execution fragment of
     * {@code ts}.
     */
    // TODO: עשיתי כאן הנחה שהמקטע ריצה מסתיים במצב ולא בפעולה (יעני שהוא תקין) - לבדוק אם מותר להניח זאת
    //TODO: מקטע ריצה שיש בו מצב אחד ו0 פעולות (יעני פשוט מצב) הוא מקטע ריצה חוקי? לטפל בהתאם
    public <S, A, P> boolean isExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        if (e.size() == 0)
            return false;
        while (e.size() > 0) {
            S from = e.head();
            AlternatingSequence<A, S> tail = e.tail(); //action and then next state
            A action = tail.head();
            e = tail.tail();
            S to = e.head();
            if (!(ts.getStates().contains(from) && ts.getStates().contains(to) && ts.getTransitions().contains(new TSTransition(from, action, to))))
                return false;
        }
        return true;
    }

    /**
     * Checks whether an alternating sequence is an initial execution fragment
     * of a {@link TransitionSystem}, as defined in class.
     *
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param <P> Type of atomic propositions.
     * @param ts  The transition system being tested.
     * @param e   The sequence that may or may not be an initial execution
     *            fragment of {@code ts}.
     * @return {@code true} iff {@code e} is an execution fragment of
     * {@code ts}.
     */
    public <S, A, P> boolean isInitialExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        return isExecutionFragment(ts, e) && ts.getInitialStates().contains(e.head());
    }

    /**
     * Checks whether an alternating sequence is a maximal execution fragment of
     * a {@link TransitionSystem}, as defined in class.
     *
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param <P> Type of atomic propositions.
     * @param ts  The transition system being tested.
     * @param e   The sequence that may or may not be a maximal execution fragment
     *            of {@code ts}.
     * @return {@code true} iff {@code e} is a maximal fragment of {@code ts}.
     */
    public <S, A, P> boolean isMaximalExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        return isExecutionFragment(ts, e) && isStateTerminal(ts, getLastState(e));
    }

    private <A, S> S getLastState(AlternatingSequence<S,A> e) {
        while(e.size() > 1) {
            e = e.tail().tail(); //skip the current state and action
        }
        return e.head();
    }

    /**
     * Checks whether a state in {@code ts} is terminal.
     *
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param ts  Transition system of {@code s}.
     * @param s   The state being tested for terminality.
     * @return {@code true} iff state {@code s} is terminal in {@code ts}.
     * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
     */
    public <S, A> boolean isStateTerminal(TransitionSystem<S, A, ?> ts, S s) {
        if (!ts.getStates().contains(s))
            throw new StateNotFoundException(s);
        return post(ts, s).size() == 0;
    }

    /**
     * @param <S> Type of states.
     * @param ts  Transition system of {@code s}.
     * @param s   A state in {@code ts}.
     * @return All the states in {@code Post(s)}, in the context of {@code ts}.
     * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
     */
    public <S> Set<S> post(TransitionSystem<S, ?, ?> ts, S s) {
        if (!ts.getStates().contains(s))
            throw new StateNotFoundException(s);
        Set<? extends TSTransition<S, ?>> transitions = ts.getTransitions();
        Set<S> post_states = new HashSet<>();
        for (TSTransition<S, ?> transition : transitions) {
            if (transition.getFrom().equals(s))
                post_states.add(transition.getTo());
        }
        return post_states;
    }

    /**
     * @param <S> Type of states.
     * @param ts  Transition system of {@code s}.
     * @param c   States in {@code ts}.
     * @return All the states in {@code Post(s)} where {@code s} is a member of
     * {@code c}, in the context of {@code ts}.
     * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
     */
    public <S> Set<S> post(TransitionSystem<S, ?, ?> ts, Set<S> c) {
        Set<S> all_post = new HashSet<>();
        for (S state : c)
            all_post.addAll(post(ts, state));
        return all_post;
    }

    /**
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param ts  Transition system of {@code s}.
     * @param s   A state in {@code ts}.
     * @param a   An action.
     * @return All the states that {@code ts} might transition to from
     * {@code s}, when action {@code a} is selected.
     * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
     */
    public <S, A> Set<S> post(TransitionSystem<S, A, ?> ts, S s, A a) {
        if (!ts.getStates().contains(s))
            throw new StateNotFoundException(s);
        Set<? extends TSTransition<S, A>> transitions = ts.getTransitions();
        Set<S> post_states = new HashSet<>();
        for (TSTransition<S, A> transition : transitions) {
            if (transition.getFrom().equals(s) && transition.getAction().equals(a))
                post_states.add(transition.getTo());
        }
        return post_states;
    }

    /**
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param ts  Transition system of {@code s}.
     * @param c   Set of states in {@code ts}.
     * @param a   An action.
     * @return All the states that {@code ts} might transition to from any state
     * in {@code c}, when action {@code a} is selected.
     */
    public <S, A> Set<S> post(TransitionSystem<S, A, ?> ts, Set<S> c, A a) {
        Set<S> all_post = new HashSet<>();
        for (S state : c)
            all_post.addAll(post(ts, state, a));
        return all_post;
    }

    /**
     * @param <S> Type of states.
     * @param ts  Transition system of {@code s}.
     * @param s   A state in {@code ts}.
     * @return All the states in {@code Pre(s)}, in the context of {@code ts}.
     */
    public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, S s) {
        Set<? extends TSTransition<S, ?>> transitions = ts.getTransitions();
        Set<S> pre_states = new HashSet<>();
        for (TSTransition<S, ?> transition : transitions) {
            if (transition.getTo().equals(s))
                pre_states.add(transition.getFrom());
        }
        return pre_states;
    }

    /**
     * @param <S> Type of states.
     * @param ts  Transition system of {@code s}.
     * @param c   States in {@code ts}.
     * @return All the states in {@code Pre(s)} where {@code s} is a member of
     * {@code c}, in the context of {@code ts}.
     * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
     */
    public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, Set<S> c) {
        Set<S> all_pre = new HashSet<>();
        for (S state : c) {
            if (!ts.getStates().contains(state))
                throw new StateNotFoundException(state);
            all_pre.addAll(pre(ts, state));
        }
        return all_pre;
    }

    /**
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param ts  Transition system of {@code s}.
     * @param s   A state in {@code ts}.
     * @param a   An action.
     * @return All the states that {@code ts} might transitioned from, when in
     * {@code s}, and the last action was {@code a}.
     * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
     */
    public <S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, S s, A a) {
        if (!ts.getStates().contains(s))
            throw new StateNotFoundException(s);
        Set<? extends TSTransition<S, A>> transitions = ts.getTransitions();
        Set<S> pre_states = new HashSet<>();
        for (TSTransition<S, A> transition : transitions) {
            if (transition.getTo().equals(s) && transition.getAction().equals(a))
                pre_states.add(transition.getFrom());
        }
        return pre_states;
    }

    /**
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param ts  Transition system of {@code s}.
     * @param c   Set of states in {@code ts}.
     * @param a   An action.
     * @return All the states that {@code ts} might transitioned from, when in
     * any state in {@code c}, and the last action was {@code a}.
     * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
     */
    public <S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, Set<S> c, A a) {
        Set<S> all_pre = new HashSet<>();
        for (S state : c)
            all_pre.addAll(pre(ts, state, a));
        return all_pre;
    }

    /**
     * Implements the {@code reach(TS)} function.
     *
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param ts  Transition system of {@code s}.
     * @return All states reachable in {@code ts}.
     */
    //TODO: test me!!!
    public <S, A> Set<S> reach(TransitionSystem<S, A, ?> ts) {
        Set<AlternatingSequence<S, A>> initialExecutionFragments = getInitialExecutionFragments(ts);
        Set<S> reach = new HashSet<>();
        for(AlternatingSequence<S, A> ief: initialExecutionFragments) {
            S lastState = getLastState(ief);
            reach.add(lastState);
        }
        return reach;
    }

    //****** Reach helpers START *******

    private <S, A> Set<AlternatingSequence<S, A>> getInitialExecutionFragments(TransitionSystem<S, A, ?> ts) {
        Set<AlternatingSequence<S, A>> res = new HashSet<>();
        Set<S> initials = ts.getInitialStates();
        for(S iState: initials){
            Set<AlternatingSequence<S, A>> exFrag = getExecutionFragmentsFromState(ts, iState);
            res.addAll(exFrag); //union
        }
        return res;
    }

    private <S, A> Set<AlternatingSequence<S, A>> getExecutionFragmentsFromState(TransitionSystem<S, A, ?> ts, S state) {
        Map<S, Boolean> isVisited = new HashMap<>();
        //prepare the result path (finally will become an AlternatingSequence)
        Path<S, A> localPath = new Path<>();
        localPath.addState(state);
        //prepare isVisited
        for (S s: ts.getStates())
            isVisited.put(s, false);

        Set<AlternatingSequence<S, A>> result = new HashSet<>();
        recurseGetExecutionFragmentsFromState(ts, state, isVisited, localPath, result);
        return result;
    }

    //TODO: i assume that the're are no circles because if there were, there would be infinite ExecutionFragments
    //a DFS implementation
    //localPath saves the current computed path and then turns into AlternatingSequence and added to the result
    private <S, A> void recurseGetExecutionFragmentsFromState(TransitionSystem<S, A, ?> ts, S state, Map<S, Boolean> isVisited, Path<S, A> localPath, Set<AlternatingSequence<S, A>> result) {
        isVisited.put(state, true);

        //save any path you've reached to
        //make an AlternatingSequence from localPath
        AlternatingSequence<S, A> patSeq = new AlternatingSequence(localPath.getStates(), localPath.getActions());
        result.add(patSeq);

        //end the recursion if the state is terminal
        if (isStateTerminal(ts, state)) {
            isVisited.put(state, false);
            return;
        }

        Set<TSTransition<S, A>> transitionsFromState = getTransitionsFrom(ts, state);
        for(TSTransition<S, A> trans: transitionsFromState) {
            S neighbor = trans.getTo();
            if (!isVisited.get(neighbor)) {
                //store current state and action n localPath
                localPath.addState(neighbor);
                localPath.addAction(trans.getAction());

                recurseGetExecutionFragmentsFromState(ts, neighbor, isVisited, localPath, result);

                //remove current state and action
                localPath.removeLastState();
                localPath.removeLastAction();
            }
        }
        isVisited.put(state, false);
    }

    //****** Reach helpers END *******

    private class Path<S, A> {
        private List<S> states;
        private List<A> actions;

        public <S, A> Path() {
            this.states = new ArrayList<>();
            this.actions = new ArrayList<>();
        }

        public List<S> getStates(){
            return this.states;
        }

        public List<A> getActions(){
            return this.actions;
        }

        public void addState(S state) {
            this.states.add(state);
        }

        public void addAction(A action) {
            this.actions.add(action);
        }

        public void removeLastState(){
            this.states.remove(this.states.size() - 1);
        }

        public void removeLastAction(){
            this.actions.remove(this.actions.size() - 1);
        }
    }

    private <S, A> Set<TSTransition<S, A>> getTransitionsFrom(TransitionSystem<S, A, ?> ts, S state) {
        Set<TSTransition<S, A>> tsTransitions = ts.getTransitions();
        Set<TSTransition<S, A>> res = new HashSet<>();
        for (TSTransition trans : tsTransitions) {
            if (trans.getFrom().equals(state))
                res.add(trans);
        }
        return res;
    }

    private <S, S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleaveHelper(TransitionSystem<S1, A, P> ts1,
                                                                                    TransitionSystem<S2, A, P> ts2, Handler handler1, Handler handler2) {
        TransitionSystem<Pair<S1, S2>, A, P> interleaveTs = new TransitionSystem<>();
        interleaveTs.addAllStates(cartesian_set(ts1.getStates(), ts2.getStates()));
        Set<A> ts1Actions = new HashSet<>(ts1.getActions());
        ts1Actions.addAll(ts2.getActions());
        interleaveTs.addAllActions(ts1Actions);
        Set<Pair<S1, S2>> allInitialStates = cartesian_set(ts1.getInitialStates(), ts2.getInitialStates());
        for (Pair<S1, S2> initialState : allInitialStates)
            interleaveTs.addInitialState(initialState);

        Set<TSTransition<Pair<S1, S2>, A>> transitionsByFirst = getTransitions(ts1, interleaveTs.getStates(),
                handler1, true);
        Set<TSTransition<Pair<S1, S2>, A>> transitionsBySecond = getTransitions(ts2, interleaveTs.getStates(),
                handler2, false);
        for (TSTransition<Pair<S1, S2>, A> transition : transitionsByFirst)
            interleaveTs.addTransition(transition);
        for (TSTransition<Pair<S1, S2>, A> transition : transitionsBySecond)
            interleaveTs.addTransition(transition);


        Set<P> ts1AtomicPropositions = new HashSet<>(ts1.getAtomicPropositions());
        ts1AtomicPropositions.addAll(ts2.getAtomicPropositions());
        interleaveTs.addAllAtomicPropositions(ts1AtomicPropositions);
        for (Pair<S1, S2> state : interleaveTs.getStates()) {
            Set<P> allPropositions = new HashSet<>(ts1.getLabel(state.getFirst()));
            Set<P> prop2 = ts2.getLabel(state.getSecond());
            allPropositions.addAll(prop2);
            for (P proposition : allPropositions)
                interleaveTs.addToLabel(state, proposition);
        }
        return interleaveTs;
    }

    /**
     * Compute the synchronous product of two transition systems.
     *
     * @param <S1> Type of states in the first system.
     * @param <S2> Type of states in the first system.
     * @param <A>  Type of actions (in both systems).
     * @param <P>  Type of atomic propositions (in both systems).
     * @param ts1  The first transition system.
     * @param ts2  The second transition system.
     * @return A transition system that represents the product of the two.
     */
    public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1,
                                                                          TransitionSystem<S2, A, P> ts2) {
        TransitionSystem<Pair<S1, S2>, A, P> interleaveTs = interleaveHelper(ts1, ts2, new Handler() {
            @Override
            public Set<Pair> getPairs(TSTransition originalTransition, Pair fromState) {
                return new HashSet<>(Arrays.asList(new Pair(originalTransition.getTo(), fromState.getSecond())));
            }
        }, new Handler() {
            @Override
            public Set<Pair> getPairs(TSTransition originalTransition, Pair fromState) {
                return new HashSet<>(Arrays.asList(new Pair(fromState.getFirst(), originalTransition.getTo())));
            }
        });
        return interleaveTs;
    }

    /**
     * Compute the synchronous product of two transition systems.
     *
     * @param <S1>               Type of states in the first system.
     * @param <S2>               Type of states in the first system.
     * @param <A>                Type of actions (in both systems).
     * @param <P>                Type of atomic propositions (in both systems).
     * @param ts1                The first transition system.
     * @param ts2                The second transition system.
     * @param handShakingActions Set of actions both systems perform together.
     * @return A transition system that represents the product of the two.
     */
    public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1,
                                                                          TransitionSystem<S2, A, P> ts2, Set<A> handShakingActions) {
        TransitionSystem<Pair<S1, S2>, A, P> interleaveTs = interleaveHelper(ts1, ts2, new Handler() {
            @Override
            public Set<Pair> getPairs(TSTransition originalTransition, Pair fromState) {
                if (!handShakingActions.contains(originalTransition.getAction()))
                    return new HashSet<>(Arrays.asList(new Pair(originalTransition.getTo(), fromState.getSecond())));
                else {
                    Set<TSTransition> fittingTransitions = getRelevantTransitions(originalTransition, fromState.getSecond(), ts2);
                    Set<Pair> toStates = new HashSet<>();
                    for (TSTransition<S2, A> trans : fittingTransitions)
                        if (trans != null)
                            toStates.add(new Pair(originalTransition.getTo(), trans.getTo()));
                    return toStates;
                }
            }
        }, new Handler() {
            @Override
            public Set<Pair> getPairs(TSTransition originalTransition, Pair fromState) {
                if (!handShakingActions.contains(originalTransition.getAction()))
                    return new HashSet<>(Arrays.asList(new Pair(fromState.getFirst(), originalTransition.getTo())));
                else {
                    Set<TSTransition> fittingTransitions = getRelevantTransitions(originalTransition, fromState.getSecond(), ts1);
                    Set<Pair> toStates = new HashSet<>();
                    for (TSTransition<S1, A> trans : fittingTransitions)
                        if (trans != null)
                            toStates.add(new Pair(trans.getTo(), originalTransition.getTo()));
                    return toStates;
                }
            }
        });
        return interleaveTs;
    }

    /**
     * Creates a new {@link ProgramGraph} object.
     *
     * @param <L> Type of locations in the graph.
     * @param <A> Type of actions of the graph.
     * @return A new program graph instance.
     */
    public <L, A> ProgramGraph<L, A> createProgramGraph() {
        return new ProgramGraph<>();
    }

    private <L1, L2, A> ProgramGraph<Pair<L1, L2>, A> interleaveHelper(ProgramGraph<L1, A> pg1, ProgramGraph<L2, A> pg2, HandlerPG handler1, HandlerPG handler2) {
        ProgramGraph<Pair<L1, L2>, A> interleaveGraph = createProgramGraph();
        //locations = locations1 * locations2
        Set<Pair<L1, L2>> locations = cartesian_set(pg1.getLocations(), pg2.getLocations());
        for (Pair<L1, L2> location : locations)
            interleaveGraph.addLocation(location);

        //initial_loc = initial_loc1 * initial_loc2
        Set<Pair<L1, L2>> initialLocations = cartesian_set(pg1.getInitialLocations(), pg2.getInitialLocations());
        for (Pair<L1, L2> location : initialLocations)
            interleaveGraph.setInitial(location, true);

        //actions = actions1 + actions2
        Set<A> pg1Actions = new HashSet<A>(pg1.getActions());
        pg1Actions.addAll(pg2.getActions());

        //transitions
        Set<PGTransition<Pair<L1, L2>, A>> transitionsByFirst = getTransitionsPG(pg1, interleaveGraph.getLocations(),
                handler1, true);
        Set<PGTransition<Pair<L1, L2>, A>> transitionsBySecond = getTransitionsPG(pg2, interleaveGraph.getLocations(),
                handler2, false);
        for (PGTransition<Pair<L1, L2>, A> transition : transitionsByFirst)
            interleaveGraph.addTransition(transition);
        for (PGTransition<Pair<L1, L2>, A> transition : transitionsBySecond)
            interleaveGraph.addTransition(transition);

        //g = g0 * g1
        Set<List<String>> initializations = cartesian_initizalizations(pg1.getInitalizations(), pg2.getInitalizations());
        for (List<String> initial : initializations)
            interleaveGraph.addInitalization(initial);

        return interleaveGraph;
    }


    /**
     * Interleaves two program graphs.
     *
     * @param <L1> Type of locations in the first graph.
     * @param <L2> Type of locations in the second graph.
     * @param <A>  Type of actions in BOTH GRAPHS.
     * @param pg1  The first program graph.
     * @param pg2  The second program graph.
     * @return Interleaved program graph.
     */
    public <L1, L2, A> ProgramGraph<Pair<L1, L2>, A> interleave(ProgramGraph<L1, A> pg1, ProgramGraph<L2, A> pg2) {
        ProgramGraph<Pair<L1, L2>, A> interleaveTs = interleaveHelper(pg1, pg2, new HandlerPG() {
            @Override
            public Set<Pair> getPairs(PGTransition originalTransition, Pair fromState) {
                return new HashSet<>(Arrays.asList(new Pair(originalTransition.getTo(), fromState.getSecond())));
            }
        }, new HandlerPG() {
            @Override
            public Set<Pair> getPairs(PGTransition originalTransition, Pair fromState) {
                return new HashSet<>(Arrays.asList(new Pair(fromState.getFirst(), originalTransition.getTo())));
            }
        });
        return interleaveTs;
    }


    /**
     * Creates a {@link TransitionSystem} representing the passed circuit.
     *
     * @param c The circuit to translate into a {@link TransitionSystem}.
     * @return A {@link TransitionSystem} representing {@code c}.
     */
    public TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> transitionSystemFromCircuit(
            Circuit c) {
        TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> transitionSystem = new TransitionSystem<>();

        //states
        Set<Map<String, Boolean>> inputsLabels = binaryPermAsMap(c.getInputPortNames());
        Set<Map<String, Boolean>> registersLabels = binaryPermAsMap(c.getRegisterNames());
        Set<Pair<Map<String, Boolean>, Map<String, Boolean>>> states = cartesian_set(registersLabels, inputsLabels);
        transitionSystem.addAllStates(states);
        //actions
        Set<Map<String, Boolean>> actions = binaryPermAsMap(c.getInputPortNames());
        transitionSystem.addAllActions(actions);
        //initialStates
        Map<String, Boolean> registersMap = new HashMap<>();
        for (String reg : c.getRegisterNames())
            registersMap.put(reg, false);
        Set<Map<String, Boolean>> initRegisters = new HashSet<Map<String, Boolean>>();
        initRegisters.add(registersMap);
        Set<Map<String, Boolean>> initInputs = binaryPermAsMap(c.getInputPortNames());
        Set<Pair<Map<String, Boolean>, Map<String, Boolean>>> initialStates = cartesian_set(initRegisters, initInputs);
        for (Pair<Map<String, Boolean>, Map<String, Boolean>> initialState : initialStates)
            transitionSystem.addInitialState(initialState);

        //transitions
        for (Pair<Map<String, Boolean>, Map<String, Boolean>> state : transitionSystem.getStates()) {
            Map<String, Boolean> inputMap = state.getSecond();
            for (String input : c.getInputPortNames()) {
                Set<Map<String, Boolean>> relevantActions = new HashSet<>();
                for (int i = 0; i < 2; i++) { //true and false
                    Map<String, Boolean> relevantAction = new HashMap<>(inputMap);
                    relevantAction.replace(input, i == 1);
                    relevantActions.add(relevantAction);
                }
                for (Map<String, Boolean> relevantAction : relevantActions) {
                    Pair<Map<String, Boolean>, Map<String, Boolean>> toState = new Pair<Map<String, Boolean>, Map<String, Boolean>>(c.updateRegisters(state.getSecond(), state.getFirst()), relevantAction);
                    transitionSystem.addTransitionFrom(state).action(relevantAction).to(toState);
                }
            }
        }
        //atomic propositions
        List atomicPropositions = new LinkedList();
        atomicPropositions.addAll(c.getInputPortNames());
        atomicPropositions.addAll(c.getOutputPortNames());
        atomicPropositions.addAll(c.getRegisterNames());
        transitionSystem.addAllAtomicPropositions(atomicPropositions);

        //labeling function
        for (Pair<Map<String, Boolean>, Map<String, Boolean>> state : transitionSystem.getStates()) {
            Map<String, Boolean> inputs = state.getSecond();
            Map<String, Boolean> registers = state.getFirst();
            Map<String, Boolean> outputs = c.computeOutputs(inputs,registers);
            List<String> relevantAPs = new LinkedList<String>();
            relevantAPs.addAll(getRelevantAPS(inputs));
            relevantAPs.addAll(getRelevantAPS(registers));
            relevantAPs.addAll(getRelevantAPS(outputs));
            transitionSystem.addToLabel(state, relevantAPs);
        }
        return transitionSystem;
    }

    /**
     * Creates a {@link TransitionSystem} from a program graph.
     *
     * @param <L>           Type of program graph locations.
     * @param <A>           Type of program graph actions.
     * @param pg            The program graph to be translated into a transition system.
     * @param actionDefs    Defines the effect of each action.
     * @param conditionDefs Defines the conditions (guards) of the program
     *                      graph.
     * @return A transition system representing {@code pg}.
     */
    public <L, A> TransitionSystem<Pair<L, Map<String, Object>>, A, String> transitionSystemFromProgramGraph(
            ProgramGraph<L, A> pg, Set<ActionDef> actionDefs, Set<ConditionDef> conditionDefs) {
        throw new java.lang.UnsupportedOperationException();
    }

    /**
     * Creates a transition system representing channel system {@code cs}.
     *
     * @param <L> Type of locations in the channel system.
     * @param <A> Type of actions in the channel system.
     * @param cs  The channel system to be translated into a transition system.
     * @return A transition system representing {@code cs}.
     */
    public <L, A> TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> transitionSystemFromChannelSystem(
            ChannelSystem<L, A> cs) {
        throw new java.lang.UnsupportedOperationException();
    }

    /**
     * Construct a program graph from nanopromela code.
     *
     * @param filename The nanopromela code.
     * @return A program graph for the given code.
     * @throws Exception If the code is invalid.
     */
    public ProgramGraph<String, String> programGraphFromNanoPromela(String filename) throws Exception {
        throw new java.lang.UnsupportedOperationException();
    }

    /**
     * Construct a program graph from nanopromela code.
     *
     * @param nanopromela The nanopromela code.
     * @return A program graph for the given code.
     * @throws Exception If the code is invalid.
     */
    public ProgramGraph<String, String> programGraphFromNanoPromelaString(String nanopromela) throws Exception {
        throw new java.lang.UnsupportedOperationException();
    }

    /**
     * Construct a program graph from nanopromela code.
     *
     * @param inputStream The nanopromela code.
     * @return A program graph for the given code.
     * @throws Exception If the code is invalid.
     */
    public ProgramGraph<String, String> programGraphFromNanoPromela(InputStream inputStream) throws Exception {
        throw new java.lang.UnsupportedOperationException();
    }

    /**
     * Creates a transition system from a transition system and an automaton.
     *
     * @param <Sts>  Type of states in the transition system.
     * @param <Saut> Type of states in the automaton.
     * @param <A>    Type of actions in the transition system.
     * @param <P>    Type of atomic propositions in the transition system, which is
     *               also the type of the automaton alphabet.
     * @param ts     The transition system.
     * @param aut    The automaton.
     * @return The product of {@code ts} with {@code aut}.
     */
    public <Sts, Saut, A, P> TransitionSystem<Pair<Sts, Saut>, A, Saut> product(TransitionSystem<Sts, A, P> ts,
                                                                                Automaton<Saut, P> aut) {
        throw new java.lang.UnsupportedOperationException();
    }

    /**
     * Verify that a system satisfies an omega regular property.
     *
     * @param <S>    Type of states in the transition system.
     * @param <Saut> Type of states in the automaton.
     * @param <A>    Type of actions in the transition system.
     * @param <P>    Type of atomic propositions in the transition system, which is
     *               also the type of the automaton alphabet.
     * @param ts     The transition system.
     * @param aut    A Büchi automaton for the words that do not satisfy the
     *               property.
     * @return A VerificationSucceeded object or a VerificationFailed object
     * with a counterexample.
     */
    public <S, A, P, Saut> VerificationResult<S> verifyAnOmegaRegularProperty(TransitionSystem<S, A, P> ts,
                                                                              Automaton<Saut, P> aut) {
        throw new java.lang.UnsupportedOperationException();
    }

    /**
     * Translation of Linear Temporal Logic (LTL) formula to a Nondeterministic
     * Büchi Automaton (NBA).
     *
     * @param <L> Type of resultant automaton transition alphabet
     * @param ltl The LTL formula represented as a parse-tree.
     * @return An automaton A such that L_\omega(A)=Words(ltl)
     */
    public <L> Automaton<?, L> LTL2NBA(LTL<L> ltl) {
        throw new java.lang.UnsupportedOperationException();
    }

    /**
     * A translation of a Generalized Büchi Automaton (GNBA) to a
     * Nondeterministic Büchi Automaton (NBA).
     *
     * @param <L>    Type of resultant automaton transition alphabet
     * @param mulAut An automaton with a set of accepting states (colors).
     * @return An equivalent automaton with a single set of accepting states.
     */
    public <L> Automaton<?, L> GNBA2NBA(MultiColorAutomaton<?, L> mulAut) {
        throw new java.lang.UnsupportedOperationException();
    }


//********************************* UTILITIES *****************************************

    private interface Handler<S1, S2> {
        Set<Pair<S1, S2>> getPairs(TSTransition originalTransition, Pair fromState);
    }

    private interface HandlerPG<L1, L2> {
        Set<Pair<L1, L2>> getPairs(PGTransition originalTransition, Pair fromState);

    }

    private Set<TSTransition> getRelevantTransitions(TSTransition originalTransition, Object fromState, TransitionSystem ts) {
        Set<TSTransition> tsTransitions = ts.getTransitions();
        Set<TSTransition> tsRelevantTransitions = new HashSet<>();
        for (TSTransition trans : tsTransitions) {
            if (trans.getFrom().equals(fromState) && trans.getAction().equals(originalTransition.getAction()))
                tsRelevantTransitions.add(trans);
        }
        return tsRelevantTransitions;
    }


    private static <S, S1, S2> Set<Pair<S1, S2>> getAllRelevantPairStates(S from, Set<Pair<S1, S2>> states, boolean isFirst) {
        Set<Pair<S1, S2>> relevantPairStates = new HashSet<>();
        for (Pair<S1, S2> state : states) {
            if (isFirst && state.getFirst().equals(from))
                relevantPairStates.add(state);
            else if (!isFirst && state.getSecond().equals(from))
                relevantPairStates.add(state);
        }
        return relevantPairStates;
    }

    private static <S, S1, S2, A, P> Set<TSTransition<Pair<S1, S2>, A>> getTransitions(TransitionSystem<S, A, P> tsOrigin, Set<Pair<S1, S2>> allStates, Handler handler, boolean isFirst) {
        Set<TSTransition<Pair<S1, S2>, A>> transitions = new HashSet<>();
        for (TSTransition<S, A> originalTransition : tsOrigin.getTransitions()) {
            Set<Pair<S1, S2>> fromStates = getAllRelevantPairStates(originalTransition.getFrom(), allStates, isFirst);
            for (Pair<S1, S2> fromState : fromStates) {
                Set<Pair<S1, S2>> toStates = handler.getPairs(originalTransition, fromState);
                for (Pair<S1, S2> toState : toStates)
                    if (toState != null)
                        transitions.add(new TSTransition<Pair<S1, S2>, A>(fromState, originalTransition.getAction(), toState));
            }
        }
        return transitions;
    }

    private <L, A, L1, L2> Set<PGTransition<Pair<L1, L2>, A>> getTransitionsPG(ProgramGraph<L, A> pgOrigin, Set<Pair<L1, L2>> locations, HandlerPG handler, boolean isFirst) {
        Set<PGTransition<Pair<L1, L2>, A>> transitions = new HashSet<>();
        for (PGTransition<L, A> originalTransition : pgOrigin.getTransitions()) {
            Set<Pair<L1, L2>> fromStates = getAllRelevantPairStates(originalTransition.getFrom(), locations, isFirst);
            for (Pair<L1, L2> fromState : fromStates) {
                Set<Pair<L1, L2>> toStates = handler.getPairs(originalTransition, fromState);
                for (Pair<L1, L2> toState : toStates)
                    if (toState != null)
                        transitions.add(new PGTransition<Pair<L1, L2>, A>(fromState, originalTransition.getCondition(), originalTransition.getAction(), toState));
            }
        }
        return transitions;
    }

    private List<String> getRelevantAPS(Map<String, Boolean> values){
        List<String> relevantAPs = new LinkedList<String>();
        for (Map.Entry<String,Boolean> input : values.entrySet())
            if (input.getValue())
                relevantAPs.add(input.getKey());
        return relevantAPs;
    }

    private static <S1, S2> Set<Pair<S1, S2>> cartesian_set(Set<S1> s1, Set<S2> s2) {
        Set<Pair<S1, S2>> cartesianSet = new HashSet<>();
        for (S1 state1 : s1)
            for (S2 state2 : s2)
                cartesianSet.add(new Pair<>(state1, state2));
        return cartesianSet;
    }

    private static Set<List<String>> cartesian_initizalizations(Set<List<String>> inits1, Set<List<String>> inits2) {
        Set<List<String>> cartesianSet = new HashSet<List<String>>();
        for (List<String> initial1 : inits1)
            for (List<String> initial2 : inits2) {
                initial1.addAll(initial2);
                cartesianSet.add(initial1);
            }
        return cartesianSet;
    }

    private static <T> Set<Set<T>> powerSet(Set<T> originalSet) {
        Set<Set<T>> sets = new HashSet<Set<T>>();
        if (originalSet.isEmpty()) {
            sets.add(new HashSet<T>());
            return sets;
        }
        List<T> list = new ArrayList<T>(originalSet);
        T head = list.get(0);
        Set<T> rest = new HashSet<T>(list.subList(1, list.size()));
        for (Set<T> set : powerSet(rest)) {
            Set<T> newSet = new HashSet<T>();
            newSet.add(head);
            newSet.addAll(set);
            sets.add(newSet);
            sets.add(set);
        }
        return sets;
    }


    private static Set<boolean[]> sets = new HashSet<>();

    private static void generateAllBinaryStrings(int n, boolean[] arr, int i) {
        if (i == n) {
            boolean newArr[] = new boolean[arr.length];
            for (int k = 0; k < arr.length; k++)
                newArr[k] = arr[k];
            sets.add(newArr);
            return;
        }
        arr[i] = false;
        generateAllBinaryStrings(n, arr, i + 1);
        arr[i] = true;
        generateAllBinaryStrings(n, arr, i + 1);
    }

    public static Set<Map<String, Boolean>> binaryPermAsMap(Set<String> inputs) {
        sets = new HashSet<>();
        generateAllBinaryStrings(inputs.size(), new boolean[inputs.size()], 0);
        Set<Map<String, Boolean>> allMaps = new HashSet<>();
        for (boolean[] set : sets) {
            Map<String, Boolean> map = new HashMap<>();
            int i = 0;
            for (String input : inputs) {
                map.put(input, set[i]);
                i++;
            }
            allMaps.add(map);
        }
        return allMaps;
    }
}
