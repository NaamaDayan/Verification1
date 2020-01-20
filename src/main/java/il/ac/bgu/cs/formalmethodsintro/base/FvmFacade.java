package il.ac.bgu.cs.formalmethodsintro.base;

import java.io.InputStream;
import java.util.*;

import il.ac.bgu.cs.formalmethodsintro.base.automata.Automaton;
import il.ac.bgu.cs.formalmethodsintro.base.automata.MultiColorAutomaton;
import il.ac.bgu.cs.formalmethodsintro.base.channelsystem.ChannelSystem;
import il.ac.bgu.cs.formalmethodsintro.base.circuits.Circuit;
import il.ac.bgu.cs.formalmethodsintro.base.exceptions.ActionNotFoundException;
import il.ac.bgu.cs.formalmethodsintro.base.exceptions.StateNotFoundException;
import il.ac.bgu.cs.formalmethodsintro.base.ltl.LTL;
import il.ac.bgu.cs.formalmethodsintro.base.nanopromela.NanoPromelaParser.*;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.*;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.AlternatingSequence;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TSTransition;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.formalmethodsintro.base.util.CollectionHelper;
import il.ac.bgu.cs.formalmethodsintro.base.util.Pair;
import il.ac.bgu.cs.formalmethodsintro.base.util.Util;
import il.ac.bgu.cs.formalmethodsintro.base.verification.VeficationSucceeded;
import il.ac.bgu.cs.formalmethodsintro.base.verification.VerificationFailed;
import il.ac.bgu.cs.formalmethodsintro.base.verification.VerificationResult;

import static il.ac.bgu.cs.formalmethodsintro.base.nanopromela.NanoPromelaFileReader.*;

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
                if ((ts.getLabelingFunction().containsKey(state) && (ts.getLabelingFunction().get(state).equals(set))) || (set.size() == 0 && ts.getLabelingFunction().size() == 0))
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
    public <S, A, P> boolean isExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        if (e.size() == 0)
            return false;
        while (e.size() > 0) {
            S from = e.head();
            if (!ts.getStates().contains(from))
                throw new StateNotFoundException(from);
            AlternatingSequence<A, S> tail = e.tail(); //action and then next state
            if (tail.size() == 0) //only one state
                return ts.getStates().contains(from);
            A action = tail.head();
            e = tail.tail();
            S to = e.head();
            if (!ts.getStates().contains(to))
                throw new StateNotFoundException(to);
            if (!ts.getActions().contains(action))
                throw new ActionNotFoundException(action);
            if (!(ts.getTransitions().contains(new TSTransition(from, action, to))))
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

    private <A, S> S getLastState(AlternatingSequence<S, A> e) {
        while (e.size() > 1) {
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
        if (!ts.getStates().contains(s))
            throw new StateNotFoundException(s);
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
        for (S state : c)
            all_pre.addAll(pre(ts, state));
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
    public <S, A> Set<S> reach(TransitionSystem<S, A, ?> ts) {
        Set<AlternatingSequence<S, A>> initialExecutionFragments = getInitialExecutionFragments(ts);
        Set<S> reach = new HashSet<>();
        for (AlternatingSequence<S, A> ief : initialExecutionFragments) {
            S lastState = getLastState(ief);
            reach.add(lastState);
        }
        return reach;
    }

    //****** Reach helpers START *******

    private <S, A> Set<AlternatingSequence<S, A>> getInitialExecutionFragments(TransitionSystem<S, A, ?> ts) {
        Set<AlternatingSequence<S, A>> res = new HashSet<>();
        Set<S> initials = ts.getInitialStates();
        for (S iState : initials) {
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
        for (S s : ts.getStates())
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
        for (TSTransition<S, A> trans : transitionsFromState) {
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

    private <S, A> Set<TSTransition<S, A>> getTransitionsFrom(TransitionSystem<S, A, ?> ts, S state) {
        Set<TSTransition<S, A>> tsTransitions = ts.getTransitions();
        Set<TSTransition<S, A>> res = new HashSet<>();
        for (TSTransition trans : tsTransitions) {
            if (trans.getFrom().equals(state))
                res.add(trans);
        }
        return res;
    }

    private class Path<S, A> {
        private List<S> states;
        private List<A> actions;

        public <S, A> Path() {
            this.states = new ArrayList<>();
            this.actions = new ArrayList<>();
        }

        public List<S> getStates() {
            return this.states;
        }

        public List<A> getActions() {
            return this.actions;
        }

        public void addState(S state) {
            this.states.add(state);
        }

        public void addAction(A action) {
            this.actions.add(action);
        }

        public void removeLastState() {
            this.states.remove(this.states.size() - 1);
        }

        public void removeLastAction() {
            this.actions.remove(this.actions.size() - 1);
        }
    }

    //****** Reach helpers END *******

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

        Set<TSTransition<Pair<S1, S2>, A>> transitionsByFirst1 = getTransitions(ts1, interleaveTs.getStates(),
                handler1, true);
        Set<TSTransition<Pair<S1, S2>, A>> transitionsBySecond = getTransitions(ts2, interleaveTs.getStates(),
                handler2, false);
        for (TSTransition<Pair<S1, S2>, A> transition : transitionsByFirst1)
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
        Set<Pair<S1, S2>> reachableStates = reach(interleaveTs);
        Set<Pair<S1, S2>> interleaveTSStates = new HashSet<>(interleaveTs.getStates());
        for (Pair<S1, S2> state : interleaveTSStates)
            if (!reachableStates.contains(state)) {
                Set<TSTransition<Pair<S1, S2>, A>> transWithState = getAllTransitionaWithState(interleaveTs, state);
                for (TSTransition<Pair<S1, S2>, A> trans : transWithState)
                    interleaveTs.removeTransition(trans);
                interleaveTs.removeState(state);
            }
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
        Set<PGTransition<Pair<L1, L2>, A>> transitionsByFirst1 = getTransitionsPG(pg1, interleaveGraph.getLocations(),
                handler1, true);
        Set<PGTransition<Pair<L1, L2>, A>> transitionsBySecond = getTransitionsPG(pg2, interleaveGraph.getLocations(),
                handler2, false);
        for (PGTransition<Pair<L1, L2>, A> transition : transitionsByFirst1)
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
        Set<Pair<Map<String, Boolean>, Map<String, Boolean>>> states = cartesian_set(inputsLabels, registersLabels);
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
        Set<Pair<Map<String, Boolean>, Map<String, Boolean>>> initialStates = cartesian_set(initInputs, initRegisters);
        for (Pair<Map<String, Boolean>, Map<String, Boolean>> initialState : initialStates)
            transitionSystem.addInitialState(initialState);

        //transitions
        for (Pair<Map<String, Boolean>, Map<String, Boolean>> state : transitionSystem.getStates()) {
            Map<String, Boolean> inputMap = state.getFirst();
            for (String input : c.getInputPortNames()) {
                Set<Map<String, Boolean>> relevantActions = new HashSet<>();
                for (int i = 0; i < 2; i++) { //true and false
                    Map<String, Boolean> relevantAction = new HashMap<>(inputMap);
                    relevantAction.replace(input, i == 1);
                    relevantActions.add(relevantAction);
                }
                for (Map<String, Boolean> relevantAction : relevantActions) {
                    Map<String, Boolean> s = c.updateRegisters(state.getFirst(), state.getSecond());
                    Pair<Map<String, Boolean>, Map<String, Boolean>> toState = new Pair<Map<String, Boolean>, Map<String, Boolean>>(relevantAction, s);
                    transitionSystem.addTransitionFrom(state).action(relevantAction).to(toState);
                }
            }
        }
        //atomic propositions
        List<Object> atomicPropositions = new LinkedList<Object>();
        atomicPropositions.addAll(c.getInputPortNames());
        atomicPropositions.addAll(c.getOutputPortNames());
        atomicPropositions.addAll(c.getRegisterNames());
        transitionSystem.addAllAtomicPropositions(atomicPropositions);

        //labeling function
        for (Pair<Map<String, Boolean>, Map<String, Boolean>> state : transitionSystem.getStates()) {
            Map<String, Boolean> inputs = state.getFirst();
            Map<String, Boolean> registers = state.getSecond();
            Map<String, Boolean> outputs = c.computeOutputs(inputs, registers);
            List<String> relevantAPs = new LinkedList<String>();
            relevantAPs.addAll(getRelevantAPS(inputs));
            relevantAPs.addAll(getRelevantAPS(registers));
            relevantAPs.addAll(getRelevantAPS(outputs));
            for (String ap : relevantAPs)
                transitionSystem.addToLabel(state, ap);
        }
        return transitionSystem;
    }

    //TODO: CHECK ME!!!

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
    //TODO: i assume that each initialization looks like "x := 15", "y:=9"
    public <L, A> TransitionSystem<Pair<L, Map<String, Object>>, A, String> transitionSystemFromProgramGraph(
            ProgramGraph<L, A> pg, Set<ActionDef> actionDefs, Set<ConditionDef> conditionDefs) {
        TransitionSystem<Pair<L, Map<String, Object>>, A, String> ts = new TransitionSystem<>();
        //initial states
        Set<Pair<L, Map<String, Object>>> initStates = new HashSet<>();
        for (L initLoc : pg.getInitialLocations()) {
            for (List<String> initialization : pg.getInitalizations()) {
                Map<String, Object> evalFun = parseInitialization(initialization, actionDefs);
                Pair<L, Map<String, Object>> state = new Pair<>(initLoc, evalFun);
                initStates.add(state); //add to local set
                addStateToTS(ts, state, true);
            }
        }
        //initial states End
        //הטקטיקה - currStates contains the states added in each level
        //We're adding new states and actions as in BFS - iterating on the new added states at each level (currStates)
        //and adding one level of state and action for each one (adding all of its neighbors)
        //do not forget at the end of each iteration empty currStates and add just the current new states
        // אם לפני שמוסיפים מצב לניו סטייטס בודקים אם הוא כבר קיים במערכת ואם כן לא מוסיפים,
        // זה יהיה יותר יעיל ונדמה לי שגם ימנע לולאה אינסופית במקרה של מעבר עצמי
        Set<Pair<L, Map<String, Object>>> currStates = new HashSet<>(initStates); //the current BFS states from which we compute the next level states
        Set<Pair<L, Map<String, Object>>> newStates = new HashSet<>(); //local next level states (neighbors of currStates)
        while (true) {
            for (Pair<L, Map<String, Object>> state : currStates) {
                Set<PGTransition<L, A>> neighborsTrans = getNeighborsTransitionsPG(pg, state.getFirst());
                for (PGTransition<L, A> trans : neighborsTrans) {
                    if (isHoldingCondition(state.getSecond(), trans.getCondition(), conditionDefs)) {
                        ActionDef action = getAction(actionDefs, trans.getAction());
                        Map<String, Object> newEval = action.effect(state.getSecond(), trans.getAction());
                        Pair<L, Map<String, Object>> newState = new Pair<>(trans.getTo(), newEval);
                        if (!ts.getStates().contains(newState)) {
                            addStateToTS(ts, newState, false);
                            newStates.add(newState);
                        }
                        ts.addTransitionFrom(state).action(trans.getAction()).to(newState);
                    }
                }
            }
            currStates = new HashSet<>(newStates);
            newStates = new HashSet<>();
            if (currStates.isEmpty())
                break;
        }
        return ts;
    }

    //searching the appropriate condition (if a condition doesn't match evaluate returns false and the iteration
    // continues to the next CondDef (that defines a condition "shape")).
    // When founds the appropriate condition, evaluates it and returns its result
    private boolean isHoldingCondition(Map<String, Object> eval, String condition, Set<ConditionDef> conditionDefs) {
        for (ConditionDef cond : conditionDefs) {
            if (cond.evaluate(eval, condition))
                return true;
        }
        return false;
    }


    //return the appropriate actionDef corresponding to the given action
    private <A> ActionDef getAction(Set<ActionDef> actionDefs, A action) {
        for (ActionDef actionDef : actionDefs)
            if (actionDef.isMatchingAction(action))
                return actionDef;
        try {
            throw new Exception("action not found - not supposed to happen");
        } catch (Exception e) {
            e.printStackTrace();
        }
        return null;
    }

    private <L, A> Set<PGTransition<L, A>> getNeighborsTransitionsPG(ProgramGraph<L, A> pg, L location) {
        Set<PGTransition<L, A>> ret = new HashSet<>();
        for (PGTransition<L, A> transition : pg.getTransitions())
            if (transition.getFrom().equals(location))
                ret.add(transition);
        return ret;
    }

    //Add the state and the corresponding label to the TS
    private <L, A> void addStateToTS(TransitionSystem<Pair<L, Map<String, Object>>, A, String> ts, Pair<L, Map<String, Object>> state, boolean isInitial) {
        if (isInitial)
            ts.addInitialState(state);
        else
            ts.addState(state);
        //Add Labeling
        ts.addToLabel(state, state.first.toString()); //location AP
        Map<String, Object> eval = state.getSecond();
        for (String var : eval.keySet()) {
            ts.addToLabel(state, var + " = " + eval.get(var));
        }
    }

    private Queue<String> stringToQueue(String str) {
        String replace = str.replace("[", "").replace("]", "");
        List<String> values = new ArrayList<String>(Arrays.asList(replace.split(",")));
        Queue<String> toRet = new LinkedList<>();
        for (String value : values)
            if (!value.equals(""))
                toRet.add(value);
        return toRet;
    }

    //make each initialization list of strings (shaped: "x := 15", "y:=9") to a map of string and object
    //TODO: i assume that each initialization is num := integer -> is is true that only integers????
    private Pair<String, Object> parseChannel(String initialization) {
        String[] splitted = initialization.split(":");
        String var = splitted[0];
        String val = splitted[1];
        Queue<String> lst = stringToQueue(val.substring(1));
        return new Pair<>(var, lst);
    }


    private Map<String, Object> parseInitialization(List<String> initialization, Set<ActionDef> actionDef) {
        Map<String, Object> map = new HashMap<>();
        List<String> noChannelInitializations = new LinkedList<>();
        for (String initAction : initialization) {
            if (!initAction.contains("["))
                noChannelInitializations.add(initAction);
        }
        for (String initAction : noChannelInitializations) {
            for (ActionDef action : actionDef)
                if (action.isMatchingAction(initAction))
                    map = action.effect(map, initAction);
        }
        for (String initAction : initialization) {
            if (initAction.contains("["))
                map.put(parseChannel(initAction).getFirst(), parseChannel(initAction).getSecond());
        }
        return map;
    }


    /**
     * Creates a transition system representing channel system {@code cs}.
     *
     * @param <L> Type of locations in the channel system.
     * @param <A> Type of actions in the channel system.
     * @param cs  The channel system to be translated into a transition system.
     * @return A transition system representing {@code cs}.
     */


    private <L, A> Set<Pair<List<L>, Map<String, Object>>> getInitialStates(ChannelSystem<L, A> cs, Set<ActionDef> actionDefs) {
        Set<Pair<List<L>, Map<String, Object>>> initStates = new HashSet<>();
        List<Set<Pair<Pair<L, Map<String, Object>>, Integer>>> toCartesian = new LinkedList<>();
        for (ProgramGraph<L, A> pg : cs.getProgramGraphs()) {

            Set<Pair<Pair<L, Map<String, Object>>, Integer>> statesWithInitialization = new HashSet<>();
            for (L initLoc : pg.getInitialLocations()) {
                if (pg.getInitalizations().size() == 0)
                    statesWithInitialization.add(new Pair<>(new Pair<L, Map<String, Object>>(initLoc, new HashMap<>()), Util.indexOfElement(cs.getProgramGraphs(), pg)));
                for (List<String> initialization : pg.getInitalizations()) {
                    Map<String, Object> evalFun = parseInitialization(initialization, actionDefs);
                    Pair<Pair<L, Map<String, Object>>, Integer> state = new Pair<Pair<L, Map<String, Object>>, Integer>(new Pair<>(initLoc, evalFun), Util.indexOfElement(cs.getProgramGraphs(), pg));
                    statesWithInitialization.add(state);
                }
            }
            toCartesian.add(statesWithInitialization);
        }

        List<Set<Pair<Pair<L, Map<String, Object>>, Integer>>> allStates = Util.cartesianProduct(toCartesian);
        for (Set<Pair<Pair<L, Map<String, Object>>, Integer>> state : allStates) {
            List<L> locations = new ArrayList<L>();
            Map<String, Object> vars = new HashMap<>();
            for (int ind = 0; ind < cs.getProgramGraphs().size(); ind++)
                for (Pair<Pair<L, Map<String, Object>>, Integer> partialState : state) {
                    if (partialState.getSecond() == ind) { //right loc
                        locations.add(partialState.getFirst().getFirst());
                        vars.putAll(partialState.getFirst().getSecond());
                    }
                }
            initStates.add(new Pair<>(locations, vars));
        }
        return initStates;
    }


    //returns relevant states that are not in checked states
    private <L> Set<Pair<List<L>, Map<String, Object>>> filterExistingStates(Set<Pair<List<L>, Map<String, Object>>> states, Set<Pair<List<L>, Map<String, Object>>> checkedStates) {
        Set<Pair<List<L>, Map<String, Object>>> toRet = new HashSet<>();
        for (Pair<List<L>, Map<String, Object>> state : states)
            if (!checkedStates.contains(state))
                toRet.add(state);
        return toRet;
    }

    private <L, A> Set<TSTransition<Pair<List<L>, Map<String, Object>>, A>> bfsStates(ChannelSystem<L, A> cs, Set<Pair<List<L>, Map<String, Object>>> currentStates, Set<ActionDef> actions, Set<ConditionDef> conditions, Set<TSTransition<Pair<List<L>, Map<String, Object>>, A>> allTrans, Set<Pair<List<L>, Map<String, Object>>> checkedStates) {
        if (checkedStates.containsAll(currentStates)) //go over all these states
            return allTrans;
        for (Pair<List<L>, Map<String, Object>> state : currentStates) {
            checkedStates.add(Util.stateCopy(state));
            Set<TSTransition<Pair<List<L>, Map<String, Object>>, A>> allStateTrans = new HashSet<>(getTransitionsPGs(cs, state, new HashSet<>(), actions, conditions, 0));
            allTrans.addAll(allStateTrans);
            //for every non-examined state, recurse call
            Set<Pair<List<L>, Map<String, Object>>> nextStates = filterExistingStates(getToStates(allStateTrans), checkedStates);
            Set<TSTransition<Pair<List<L>, Map<String, Object>>, A>> newTrans = new HashSet<>(bfsStates(cs, nextStates, actions, conditions, allTrans, checkedStates));
            allTrans.addAll(newTrans);
        }
        return allTrans;
    }

    private <L, A> Set<Pair<List<L>, Map<String, Object>>> getToStates(Set<TSTransition<Pair<List<L>, Map<String, Object>>, A>> transitions) {
        Set<Pair<List<L>, Map<String, Object>>> toStates = new HashSet<>();
        for (TSTransition<Pair<List<L>, Map<String, Object>>, A> trans : transitions)
            toStates.add(trans.getTo());
        return toStates;
    }


    //TODO:: change it to be n locations, not just 2, recursive function
    private <L, A> Set<TSTransition<Pair<List<L>, Map<String, Object>>, A>> getTransitionsPGs(ChannelSystem<L, A> cs, Pair<List<L>, Map<String, Object>> state, Set<TSTransition<Pair<List<L>, Map<String, Object>>, A>> transitions, Set<ActionDef> actions, Set<ConditionDef> conditions, int index) {
        if (index == cs.getProgramGraphs().size()) //go over all substates in state s
            return transitions;
        ProgramGraph<L, A> pg = cs.getProgramGraphs().get(index);
        for (PGTransition<L, A> trans : pg.getTransitions()) {
            if (trans.getFrom().equals(state.getFirst().get(index)) && isHoldingCondition(state.getSecond(), trans.getCondition(), conditions)) {
                if (trans.getAction().toString().startsWith("_")) {
                    Set<TSTransition<Pair<List<L>, Map<String, Object>>, A>> newTrans = getTransitionsHandshake(cs, state, trans, actions, conditions, index);
                    transitions.addAll(newTrans);
                }
                //transitions.add(getTransitionsActions());
                else {
                    TSTransition<Pair<List<L>, Map<String, Object>>, A> newTrans = getTransitionsChannel(state, trans, actions, index);
                    if (newTrans != null)
                        transitions.add(newTrans);
                }
            }
        }
        return getTransitionsPGs(cs, state, transitions, actions, conditions, index + 1);
    }

    private <L, A> TSTransition<Pair<List<L>, Map<String, Object>>, A> getTransitionsChannel(Pair<List<L>, Map<String, Object>> state, PGTransition<L, A> transition, Set<ActionDef> actions, int index) {
        //locs
        List<L> toStateLocs = new LinkedList<>(state.getFirst());
        toStateLocs.remove(index);
        toStateLocs.add(index, transition.getTo());
        //values
        Map<String, Object> values = new HashMap<>(Util.deepCopyM(state.getSecond()));
        values = getAction(actions, transition.getAction()).effect(values, transition.getAction());
        if (values == null) //illegal action
            return null;
        Pair<List<L>, Map<String, Object>> toState = new Pair<>(toStateLocs, values);
        return new TSTransition<>(state, transition.getAction(), toState);
    }

    private <A> A getHandshakeAction(A act1, A act2, boolean isFirst) {
        if (isFirst)
            return (A) ((String) act1 + "|" + (String) act2);
        return (A) ((String) act2 + "|" + (String) act1);

    }


    private <L, A> Set<TSTransition<Pair<List<L>, Map<String, Object>>, A>> getTransitionsHandshake(ChannelSystem<L, A> cs, Pair<List<L>, Map<String, Object>> state, PGTransition<L, A> transition, Set<ActionDef> actions, Set<ConditionDef> conditions, int index) {
        Set<TSTransition<Pair<List<L>, Map<String, Object>>, A>> newTransitions = new HashSet<>();
        for (int pgIndex2 = 0; pgIndex2 < cs.getProgramGraphs().size(); pgIndex2++) {
            if (pgIndex2 == index)
                continue;
            ProgramGraph<L, A> pg2 = cs.getProgramGraphs().get(pgIndex2);
            for (PGTransition<L, A> pg2Trans : pg2.getTransitions())
                if (isMatchingTransitions(transition, pg2Trans) && isHoldingCondition(state.getSecond(), pg2Trans.getCondition(), conditions)) {
                    List<L> toStateLocs = new LinkedList<>(state.getFirst());
                    toStateLocs.remove(index);
                    toStateLocs.add(index, transition.getTo());
                    toStateLocs.remove(pgIndex2);
                    toStateLocs.add(pgIndex2, pg2Trans.getTo());
                    Map<String, Object> values = new HashMap<>(Util.deepCopyM(state.getSecond()));
                    values = getAction(actions, transition.getAction()).effect(values, transition.getAction());
                    if (values == null) //illegal action
                        continue;
                    Pair<List<L>, Map<String, Object>> toState = new Pair<List<L>, Map<String, Object>>(toStateLocs, values);
                    A handshakeAction = getHandshakeAction(transition.getAction(), pg2Trans.getAction(), pgIndex2 > index);
                    TSTransition<Pair<List<L>, Map<String, Object>>, A> newTrans = new TSTransition<>(state, handshakeAction, toState);
                    newTransitions.add(newTrans);
                }
        }
        return newTransitions;
    }

    private <L, A> boolean isMatchingTransitions(PGTransition<L, A> pg1Trans, PGTransition<L, A> pg2Trans) {
        if (pg1Trans.getAction().toString().length() == 0 | pg2Trans.getAction().toString().length() == 0)
            return false;
        //same channels
        if (ParserBasedActDefChannel.getChannel(pg1Trans.getAction().toString()).equals(ParserBasedActDefChannel.getChannel(pg2Trans.getAction().toString()))) {
            if (pg1Trans.getAction().toString().contains("!") && pg2Trans.getAction().toString().contains("?"))
                return true;
            if (pg1Trans.getAction().toString().contains("?") && pg2Trans.getAction().toString().contains("!"))
                return true;
        }
        return false;
    }


    private <L, A> boolean isPGHasVar(String var, ProgramGraph<L, A> pg) {
        for (List<String> initialization : pg.getInitalizations())
            for (String str : initialization)
                if (str.contains(var))
                    return true;
        return false;
    }


    //given pg, return initialization which were not described :{C=[], x=0, y=1}, {C=[], x=0,y=0},...
    private <L, A> List<List<String>> parseInitializations(ProgramGraph<L, A> pg) {
        List<String> actions = new LinkedList<>();
        for (A action : pg.getActions())
            actions.add(action.toString());
        List<List<String>> finalInitializations = new LinkedList<>();
        Set<Set<String>> partialInitializations = new HashSet<>(); //{C=[]}, {x=0,x=1} , {y=1,y=0}
        for (String action : actions) {
            int ind = action.indexOf('?') == -1 ? action.indexOf('!') : action.indexOf('?');
            if (ind != -1) {
                String channel = action.substring(0, ind);
                channel = channel.substring(channel.lastIndexOf(' ') + 1);
                partialInitializations.add(CollectionHelper.set(channel + ":=[]")); //channel not a var
                String var = action.substring(ind + 1);
                if (isPGHasVar(var, pg) || var.length() == 0 || Util.isNumber(var)) //only add new vars
                    continue;

                //TODO:: check if var is a number, and if so - do not include it!!
                int cutIndex = var.indexOf(' ') != -1 ? var.indexOf(' ') : var.length();
                var = var.substring(0, cutIndex);
                //TODO:: check if initialization in 1 is needed!
                partialInitializations.add(CollectionHelper.set(var + ":=0")); //var is a var
            }
        }
        List<Set<String>> partialInitializationsList = new LinkedList<>(partialInitializations);
        List<Set<String>> initializations = Util.cartesianProduct(partialInitializationsList); //{c=[], x=0, y=0}, {c=[],x=0, y=1} ....
        for (Set<String> initialization : initializations) {
            List<String> initializationList = new LinkedList<>(initialization);
            if (!pg.getInitalizations().contains(initializationList))
                finalInitializations.add(initializationList);
        }
        return finalInitializations;
    }


    public <L, A> TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> transitionSystemFromChannelSystem(
            ChannelSystem<L, A> cs) {

        Set<ActionDef> actions = CollectionHelper.set(new ParserBasedActDef(), new ParserBasedActDefChannel());
        Set<ConditionDef> conditions = Collections.singleton(new ParserBasedCondDef());
        return transitionSystemFromChannelSystem(cs, actions, conditions);
    }


    private <L, A> TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> transitionSystemFromChannelSystem(
            ChannelSystem<L, A> cs, Set<ActionDef> actions, Set<ConditionDef> conditions) {
        TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> transitionSystem = new TransitionSystem<>();
        //states
        //add missing initializations
        for (ProgramGraph<L, A> programGraph : cs.getProgramGraphs()) {
            List<List<String>> newInitializations = parseInitializations(programGraph);
            if (programGraph.getInitalizations().size() == 0) {
                for (List<String> initialization : newInitializations)
                    programGraph.addInitalization(initialization);
            }
            //TODO:: add else - add {C=[]} to {y=0, y=1} --> {y=0, c=[]}, {y=1, c=[]}
        }
        Set<Pair<List<L>, Map<String, Object>>> initialStates = getInitialStates(cs, actions);

        for (Pair<List<L>, Map<String, Object>> state : initialStates)
            transitionSystem.addInitialState(state);
        Set<TSTransition<Pair<List<L>, Map<String, Object>>, A>> allTransitions = bfsStates(cs, initialStates, actions, conditions, new HashSet<>(), new HashSet<>());
        for (TSTransition<Pair<List<L>, Map<String, Object>>, A> trans : allTransitions)
            transitionSystem.addTransition(trans);

        //labeling function
        for (Pair<List<L>, Map<String, Object>> state : transitionSystem.getStates()) {
            Set<String> currentAtomicPropositions = mapToString(state);
            for (String ap : currentAtomicPropositions)
                transitionSystem.addToLabel(state, ap);
        }
        return transitionSystem;
    }


    private <L> Set<String> mapToString(Pair<List<L>, Map<String, Object>> state) {
        Set<String> equalityStrings = new HashSet<>();
        for (Map.Entry entry : state.getSecond().entrySet()) {
            equalityStrings.add(entry.getKey() + " = " + entry.getValue().toString());
        }
        for (L location : state.getFirst())
            equalityStrings.add(location.toString());
        return equalityStrings;
    }

    /**
     * Construct a program graph from nanopromela code.
     *
     * @param filename The nanopromela code.
     * @return A program graph for the given code.
     * @throws Exception If the code is invalid.
     */
    public ProgramGraph<String, String> programGraphFromNanoPromela(String filename) throws Exception {
        StmtContext stmt = pareseNanoPromelaFile(filename);
        return programGraphFromNanoPromela(stmt);
    }

    /**
     * Construct a program graph from nanopromela code.
     *
     * @param nanopromela The nanopromela code.
     * @return A program graph for the given code.
     * @throws Exception If the code is invalid.
     */
    public ProgramGraph<String, String> programGraphFromNanoPromelaString(String nanopromela) throws Exception {
        StmtContext stmt = pareseNanoPromelaString(nanopromela);
        return programGraphFromNanoPromela(stmt);
    }

    /**
     * Construct a program graph from nanopromela code.
     *
     * @param inputStream The nanopromela code.
     * @return A program graph for the given code.
     * @throws Exception If the code is invalid.
     */
    public ProgramGraph<String, String> programGraphFromNanoPromela(InputStream inputStream) throws Exception {
        StmtContext stmt = parseNanoPromelaStream(inputStream);
        return programGraphFromNanoPromela(stmt);
    }

    public ProgramGraph<String, String> programGraphFromNanoPromela(StmtContext root) {
        ProgramGraph<String, String> pg = createProgramGraph();
        Set<String> sub = sub(root, pg);
        pg.setInitial(root.getText(), true);
//        for (String s: toRem)
//            pg.removeLocation(s);
        //TODO: Remove unreachables???
        return pg;
    }

    private Set<String> sub(StmtContext root, ProgramGraph<String, String> pg) {
        Set<String> sub = new HashSet<>();
        subRec(root, sub, pg);
        return sub;
    }

    private static final String EXIT_STATE = ""; //TODO: "" or "exit" ???????
    private static final String TRUE_CONDITION = ""; //TODO: "" or "true" ???????
    private static final String NOTHING_ACTION = ""; //TODO: "" or "nothing" ???????
    private static final String SKIP_ACTION = "skip";

    private static Set<String> toRem = new HashSet<>();

    private void subRec(StmtContext root, Set<String> sub, ProgramGraph<String, String> pg) {
        if (root.assstmt() != null || root.chanreadstmt() != null || root.chanwritestmt() != null
                || root.atomicstmt() != null || root.skipstmt() != null) {
            sub.add(root.getText());
            sub.add(EXIT_STATE);
            addBaseCaseToPG(root, pg);
        } else if (root.ifstmt() != null) {
            sub.add(root.getText());
            sub.add(EXIT_STATE);
            for (OptionContext op : root.ifstmt().option()) {
                sub.addAll(sub(op.stmt(), pg));
                toRem.add(op.stmt().getText());
            }
            addIfStmtToPG(root.ifstmt(), pg);
        } else if (root.dostmt() != null) {
            sub.add(root.getText());
            sub.add(EXIT_STATE);
            for (OptionContext op : root.dostmt().option()) {
                Set<String> op_sub = sub(op.stmt(), pg);
                op_sub.remove(EXIT_STATE);
                for (String op_sub_i : op_sub) {
                    sub.add(op_sub_i + ';' + root.getText());
                    addConcatenationToPG(op_sub_i, root.getText(), pg); //TODO: i think it should be here either
                    toRem.add(op_sub_i + ';' + root.getText());
                }
                toRem.add(op.stmt().getText());
            }
            addDoStmtToPG(root.dostmt(), pg);
        } else { // ;
            sub.addAll(sub(root.stmt(1), pg));
            Set<String> sub_stmt_0 = sub(root.stmt(0), pg);
            sub_stmt_0.remove(EXIT_STATE);
            for (String sub_stmt_0_i : sub_stmt_0) {
                sub.add(sub_stmt_0_i + ';' + root.stmt(1).getText());
                addConcatenationToPG(sub_stmt_0_i, root.stmt(1).getText(), pg);
                toRem.add(sub_stmt_0_i);
            }
        }
    }

    private void addDoStmtToPG(DostmtContext dostmt, ProgramGraph<String, String> pg) {
        //a single transition to exit
        String notOption = "";
        for (OptionContext option : dostmt.option()) {
            if (!option.equals(TRUE_CONDITION))
                if (notOption.equals("")) //first condition
                    notOption = "!(" + option.boolexpr().getText() + ")";
                else
                    notOption += " && !(" + option.boolexpr().getText() + ")";
            pg.addTransition(new PGTransition<>(dostmt.getText(), notOption, NOTHING_ACTION, EXIT_STATE));
        }
        for (OptionContext option : dostmt.option()) {
            StmtContext subStmt = option.stmt();
            String gi = option.boolexpr().getText();
            Set<PGTransition<String, String>> subStmtTransitions = getTransitionsFrom(subStmt.getText(), pg);
            assertNotEmptyTransitionSet(subStmtTransitions);
            for (PGTransition<String, String> trans : subStmtTransitions) {
                String h = trans.getCondition();
                String condition = buildCondition(gi, h);
                if (trans.getTo().equals(EXIT_STATE))
                    pg.addTransition(new PGTransition<>(dostmt.getText(), condition, trans.getAction(), dostmt.getText()));
                else
                    pg.addTransition(new PGTransition<>(dostmt.getText(), condition, trans.getAction(), trans.getTo() + ";" + dostmt.getText()));
                //TODO: if there's a problem with FROM, maybe we need the getText() of the root(from the caller function)
                // and not of the doStmt.getText()
            }
        }
    }

    private void addIfStmtToPG(IfstmtContext ifStmt, ProgramGraph<String, String> pg) {
        for (OptionContext option : ifStmt.option()) {
            StmtContext subStmt = option.stmt();
            String gi = option.boolexpr().getText();
            Set<PGTransition<String, String>> subStmtTransitions = getTransitionsFrom(subStmt.getText(), pg);
            assertNotEmptyTransitionSet(subStmtTransitions);
            for (PGTransition<String, String> trans : subStmtTransitions) {
                String h = trans.getCondition();
                String condition = buildCondition(gi, h);
                pg.addTransition(new PGTransition<>(ifStmt.getText(), condition, trans.getAction(), trans.getTo()));
                //TODO: if there's a problem with FROM, maybe we need the getText() of the root(from the caller function)
                // and not of the ifStmt.getText()
            }
        }
    }

    private String buildCondition(String gi, String h) {
        if (gi.equals(TRUE_CONDITION)) {
            if (h.equals(TRUE_CONDITION))
                return TRUE_CONDITION;
            return h;
        } else {
            if (h.equals(TRUE_CONDITION))
                return gi;
            return "((" + gi + ") && (" + h + "))";
        }
    }

    private void addConcatenationToPG(String stmt1, String stmt2, ProgramGraph<String, String> pg) {
        Set<PGTransition<String, String>> stmt1Transitions = getTransitionsFrom(stmt1, pg);
        assertNotEmptyTransitionSet(stmt1Transitions);
        for (PGTransition<String, String> trans : stmt1Transitions) {
            String condition = trans.getCondition().equals("true") ? TRUE_CONDITION : trans.getCondition();
            if (trans.getTo().equals(EXIT_STATE))
                pg.addTransition(new PGTransition<>(stmt1 + ';' + stmt2, condition, trans.getAction(), stmt2));
            else
                pg.addTransition(new PGTransition<>(stmt1 + ';' + stmt2, condition, trans.getAction(), trans.getTo() + ';' + stmt2));
        }
    }

    private Set<PGTransition<String, String>> getTransitionsFrom(String stmt, ProgramGraph<String, String> pg) {
        Set<PGTransition<String, String>> res = new HashSet<>();
        if (!pg.getLocations().contains(stmt))
            throw new StateNotFoundException(stmt);
        Set<PGTransition<String, String>> transitions = pg.getTransitions();
        for (PGTransition<String, String> trans : transitions) {
            if (trans.getFrom().equals(stmt))
                res.add(trans);
        }
        return res;
    }

    private void addBaseCaseToPG(StmtContext root, ProgramGraph<String, String> pg) {
        String rootText = root.getText();
        String action = root.skipstmt() != null ? SKIP_ACTION
                : root.atomicstmt() != null ? rootText.substring(rootText.indexOf('{') + 1, rootText.indexOf('}'))
                : rootText;
        pg.addTransition(new PGTransition<>(root.getText(), TRUE_CONDITION, action, EXIT_STATE));
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
        TransitionSystem<Pair<Sts, Saut>, A, Saut> productTS = new TransitionSystem<>();
        productTS.addAllStates(cartesian_set(ts.getStates(), aut.getAllStates())); //TODO::: check the function getAllStates()
        productTS.addAllActions(ts.getActions());
        //transitions
        for (TSTransition<Sts, A> transition : ts.getTransitions()) { //transition = s --a--> t
            Set<P> lToState = ts.getLabelingFunction().get(transition.getTo()); // L(t)
            if (lToState == null)
                lToState = new HashSet<>();
            for (Pair<Sts, Saut> productState : productTS.getStates())
                if (productState.getFirst().equals(transition.getFrom())) {
                    Set<Saut> pVals = aut.getTransitions().get(productState.getSecond()).get(lToState); // p in delta(q,L(t))
                    if (pVals != null)
                        for (Saut pVal : pVals)
                            productTS.addTransition(new TSTransition<>(productState, transition.getAction(), new Pair<>(transition.getTo(), pVal)));
                }
        }

        //initial states
        for (Sts initialState : ts.getInitialStates()) {
            Set<P> lInitialState = ts.getLabelingFunction().get(initialState); //L(S0)
            if (lInitialState == null)
                lInitialState = new HashSet<>();
            for (Saut initialAutStatae : aut.getInitialStates()) {
                Set<Saut> toInitials = aut.getTransitions().get(initialAutStatae).get(lInitialState);
                for (Saut toInitial : toInitials)
                    productTS.addInitialState(new Pair<>(initialState, toInitial));
            }
        }
        //atomic propositions
        for (Pair<Sts, Saut> pairedState : productTS.getStates()) {
            productTS.addToLabel(pairedState, pairedState.second);
        }
        return productTS;
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
        TransitionSystem<Pair<S, Saut>, A, Saut> productTS = product(ts, aut);
        DFS<S, Saut> dfs = new DFS<>();

        Set<Pair<S, Saut>> notVisitedInitials = diff(productTS.getInitialStates(), dfs.getR());
        while (!notVisitedInitials.isEmpty() && !dfs.isFound_cycle()) {
            Pair<S, Saut> s = notVisitedInitials.iterator().next(); //TODO: is this fine to let s line in the algo?
            reachableCycle(s, dfs, productTS, aut);
            notVisitedInitials = diff(productTS.getInitialStates(), dfs.getR());
        }
        if (!dfs.isFound_cycle())
            return new VeficationSucceeded<>();
        else {
            VerificationFailed failed = new VerificationFailed();
            failed.setCycle(reverse(dfs.getV()));
            failed.setPrefix(reverse(dfs.getU()));
            return failed;
        }
    }

    private <Saut, S> List reverse(Stack<Pair<S, Saut>> stack) {
        List<Pair<S, Saut>> result = new LinkedList();
        while (!stack.isEmpty())
            result.add(stack.pop());
        return result;
    }

    private <Saut, S, A, P> void reachableCycle(Pair<S, Saut> s, DFS<S, Saut> dfs, TransitionSystem<Pair<S, Saut>, A, Saut> ts, Automaton<Saut, P> aut) {
        dfs.getU().push(s);
        dfs.getR().add(s);
        while (!(dfs.getU().isEmpty() || dfs.isFound_cycle())) {
            Pair<S, Saut> sPrime = dfs.getU().peek();
            Set<Pair<S, Saut>> reachablesNotVisited = diff(post(ts, sPrime), dfs.getR());
            if (!reachablesNotVisited.isEmpty()) {
                Pair<S, Saut> sPrimePrime = reachablesNotVisited.iterator().next(); //TODO: is this fine to let s line in the algo?
                dfs.getU().push(sPrimePrime);
                dfs.getR().add(sPrimePrime);
            } else {
                dfs.getU().pop();
                if (aut.getAcceptingStates().contains(sPrime.getSecond()))
                    dfs.setFound_cycle(cycleCheck(sPrime, dfs, ts));
            }
        }
    }

    private <Saut, S, A> boolean cycleCheck(Pair<S, Saut> s, DFS<S, Saut> dfs, TransitionSystem<Pair<S, Saut>, A, Saut> ts) {
        boolean foundCycle = false;
        dfs.getV().push(s);
        dfs.getT().add(s);
        while (!(dfs.getV().isEmpty() || foundCycle)) {
            Pair<S, Saut> sPrime = dfs.getV().peek();
            if (post(ts, sPrime).contains(s))
                foundCycle = true;
            else {
                Set<Pair<S, Saut>> diffPost = diff(post(ts, sPrime), dfs.getT()); //TODO: is this fine to let s line in the algo?
                if (!diffPost.isEmpty()) {
                    Pair<S, Saut> sPrimePrime = diffPost.iterator().next();
                    dfs.getV().push(sPrimePrime);
                    dfs.getT().add(sPrimePrime);
                } else
                    dfs.getV().pop();
            }
        }
        return foundCycle;
    }


    public <S, Saut> Set<Pair<S, Saut>> diff(Set<Pair<S, Saut>> s1, Set<Pair<S, Saut>> s2) {
        Set<Pair<S, Saut>> res = new HashSet<>();
        for (Pair<S, Saut> p : s1) {
            if (!s2.contains(p))
                res.add(p);
        }
        return res;
    }

    private class DFS<S, Saut> {
        private Set<Pair<S, Saut>> R;
        private Stack<Pair<S, Saut>> U;
        private Set<Pair<S, Saut>> T;
        private Stack<Pair<S, Saut>> V;
        private boolean found_cycle;

        public DFS() {
            R = new HashSet<>();
            U = new Stack<>();
            T = new HashSet<>();
            V = new Stack<>();
            found_cycle = false;
        }

        public Set<Pair<S, Saut>> getR() {
            return R;
        }

        public Stack<Pair<S, Saut>> getU() {
            return U;
        }

        public Set<Pair<S, Saut>> getT() {
            return T;
        }

        public Stack<Pair<S, Saut>> getV() {
            return V;
        }

        public boolean isFound_cycle() {
            return found_cycle;
        }

        public void setFound_cycle(boolean found_cycle) {
            this.found_cycle = found_cycle;
        }
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
        return GNBA2NBAHelper(mulAut);
    }

    private <State, L> Automaton<Pair<State,Integer>, L> GNBA2NBAHelper(MultiColorAutomaton<State, L> mulAut) {
        Automaton<Pair<State,Integer>, L> finalNBA = new Automaton<>();
        int numOfColors = mulAut.getColors().size();
        List<MultiColorAutomaton<Pair<State,Integer>, L>> autCopies = new LinkedList<>();
        for (int i : mulAut.getColors())
            autCopies.add(mulAut.copyAutomat(i));
        //set initials
        for (Pair<State,Integer> state : autCopies.get(0).getInitialStates())
            finalNBA.setInitial(state);
        for (Map.Entry<State, Map<Set<L>, Set<State>>> transition : mulAut.getTransitions().entrySet()) {
            for (Map.Entry<Set<L>, Set<State>> entry : transition.getValue().entrySet())
                for (State toState : entry.getValue())
                    for (int i : mulAut.getColors())
                        for (int j : mulAut.getColors()) {
                            boolean sAcceptable = mulAut.getAcceptingStates(i).contains(transition.getKey());
                            if ((!sAcceptable && j == i) || (sAcceptable && (j == i % numOfColors + 1)))
                                finalNBA.addTransition(new Pair<>(transition.getKey(),i), entry.getKey(), new Pair<>(toState, j));
                        }
        }
        //acceptance
        Set<?> accepting = new HashSet<>(autCopies.get(0).getAcceptingStates(1));
        finalNBA.addAllAccepting(accepting, 0);
        return finalNBA;
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

    private List<String> getRelevantAPS(Map<String, Boolean> values) {
        List<String> relevantAPs = new LinkedList<String>();
        for (Map.Entry<String, Boolean> input : values.entrySet())
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
                List<String> newList = new ArrayList<>(initial1);
                newList.addAll(initial2);
                cartesianSet.add(newList);
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

    private <S1, S2, A> Set<TSTransition<Pair<S1, S2>, A>> getAllTransitionaWithState(TransitionSystem<Pair<S1, S2>, A, ?> ts, Pair<S1, S2> state) {
        Set<TSTransition<Pair<S1, S2>, A>> transWithState = new HashSet<>();
        for (TSTransition<Pair<S1, S2>, A> transition : ts.getTransitions())
            if (transition.getFrom().equals(state) || transition.getTo().equals(state))
                transWithState.add(transition);
        return transWithState;
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

    private void assertNotEmptyTransitionSet(Set<PGTransition<String, String>> transitions) {
        if (transitions.isEmpty())
            try {
                throw new Exception("No transitions from a specific stmt. debug me to learn more");
            } catch (Exception e) {
                e.printStackTrace();
            }
    }

    private static <S1, S2> Set<S1> getKeysByValue(Map<S1, S2> map, S2 value) {
        Set<S1> keys = new HashSet<>();
        for (Map.Entry<S1, S2> entry : map.entrySet())
            if (entry.getValue().equals(value))
                keys.add(entry.getKey());
        return keys;
    }
}
