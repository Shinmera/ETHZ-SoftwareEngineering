package ch.ethz.sae;

import apron.*;

// Wrapper of an abstract element
public class AWrapper {

    Abstract1 elem;
    Manager man;

    public AWrapper(Abstract1 e) {
        elem = e;
    }

    public Abstract1 get() {
        return elem;
    }

    public void set(Abstract1 e) {
        elem = e;
    }

    public void copy(AWrapper src) {
        this.elem = src.get();
    }

    public boolean equals(Object o) {
        Abstract1 t = ((AWrapper) o).get();
        try {
            if (elem.isEqual(man, t) != elem.isIncluded(man, t))
                System.out.println("VIOLA");
            return elem.isIncluded(man, t);
        } catch (ApronException e) {
            System.err.println("isEqual failed");
            System.exit(-1);
        }
        return false;
    }

    public String toString() {
        try {
            if (elem.isTop(man))
                return "<Top>";

            return elem.toString();
        } catch (ApronException e) {
            System.err.println("toString failed");
            System.exit(-1);
        }
        return null;
    }
}
