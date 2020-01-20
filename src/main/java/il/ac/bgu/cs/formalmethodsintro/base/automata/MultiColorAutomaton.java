package il.ac.bgu.cs.formalmethodsintro.base.automata;

import il.ac.bgu.cs.formalmethodsintro.base.util.Pair;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

public class MultiColorAutomaton<State, L> {

    private final Set<State> initial;
    private final Map<Integer, Set<State>> accepting;
    private final Map<State, Map<Set<L>, Set<State>>> transitions;

    public MultiColorAutomaton() {
        transitions = new HashMap<>();
        initial = new HashSet<>();
        accepting = new HashMap<>();
    }

    public void addState(State s) {
        if (!transitions.containsKey(s)) {
            transitions.put(s, new HashMap<>());
        }
    }


    //Naama wrote
    public Set<State> getAllStates() {
        Set<State> states = new HashSet<>() {
        };
        states.addAll(transitions.keySet());
        for (State s : transitions.keySet()) {
            Map<Set<L>, Set<State>> statesMap = transitions.get(s);
            for (Map.Entry<Set<L>, Set<State>> entry : statesMap.entrySet()) {
                Set<State> otherState = entry.getValue();
                states.addAll(otherState);
            }
        }
        return states;
    }

    public void addTransition(State source, Set<L> symbol, State destination) {
        if (!transitions.containsKey(source)) {
            addState(source);
        }

        if (!transitions.containsKey(destination)) {
            addState(destination);
        }

        Set<State> set = transitions.get(source).get(symbol);
        if (set == null) {
            set = new HashSet<>();
            transitions.get(source).put(symbol, set);
        }
        set.add(destination);
    }

    public Set<State> getAcceptingStates(int color) {
        Set<State> acc = accepting.get(color);

        if (acc == null) {
            acc = new HashSet<>();
            accepting.put(color, acc);
        }

        return acc;
    }

    public Set<State> getInitialStates() {
        return initial;
    }

    public Map<State, Map<Set<L>, Set<State>>> getTransitions() {
        return transitions;
    }

    public Set<State> nextStates(State source, Set<L> symbol) {
        if (!transitions.containsKey(source)) {
            throw new IllegalArgumentException();
        } else {
            return transitions.get(source).get(symbol);
        }
    }

    public void setAccepting(State s, int color) {
        Set<State> acc = accepting.get(color);

        if (acc == null) {
            acc = new HashSet<>();
            accepting.put(color, acc);
        }

        addState(s);
        acc.add(s);
    }

    public void addAllAccepting(Set<?> states, int color) {
        for (Object state : states)
            setAccepting((State) state, color);
    }


    public void setInitial(State s) {
        addState(s);
        initial.add(s);
    }

    //Our function
    public void addInitial(Object s) {
        addState((State) s);
        initial.add((State) s);
    }

    public Set<Integer> getColors() {
        return accepting.keySet();
    }

    @Override
    public int hashCode() {
        int hash = 7;
        hash = 53 * hash + Objects.hashCode(this.initial);
        hash = 53 * hash + Objects.hashCode(this.accepting);
        return hash;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (getClass() != obj.getClass()) {
            return false;
        }
        final MultiColorAutomaton<?, ?> other = (MultiColorAutomaton<?, ?>) obj;
        if (!Objects.equals(this.initial, other.initial)) {
            return false;
        }
        if (!Objects.equals(this.accepting, other.accepting)) {
            return false;
        }
        return Objects.equals(this.transitions, other.transitions);
    }


    public MultiColorAutomaton<State, L> copyAutomat(int i) {
        MultiColorAutomaton<State, L> copyAut = new MultiColorAutomaton<>();
        //initials
        for (State state : this.getInitialStates())
            copyAut.setInitial((State)((String)state + i));
        //transitions
        for (Map.Entry<State, Map<Set<L>, Set<State>>> entry : transitions.entrySet()) {
            Map<Set<L>, Set<State>> values = new HashMap<>(entry.getValue());
            for (Map.Entry<Set<L>, Set<State>> value : values.entrySet())
                for (State toState : value.getValue())
                    copyAut.addTransition((State)((String)entry.getKey() + i), value.getKey(), (State)((String)toState + i));
        }

        //acceptance
        for (State s : accepting.get(i))
            copyAut.setAccepting((State)((String)s + i), i);
        return copyAut;
    }

}
