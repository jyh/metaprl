/**
 * A meta-pair.
 */
public abstract class ParamMPair
extends Param
{
    /**
     * Two subterms.
     */
    Param param1, param2;

    /**
     * Matching is not possible.
     */
    Param match(Param param2)
        throws ParamMatchError
    {
        throw new ParamMatchError("Can't match a compute parameter", this, param2);
    }

    /**
     * Make the number var.
     */
    public ParamMPair(Param param1, Param param2)
    {
        this.param1 = param1;
        this.param2 = param2;
    }
}

/*
 * $Log$
 * Revision 1.1  1998/02/05 15:47:12  jyh
 * This is a simple term display in an applet.
 *
 */
