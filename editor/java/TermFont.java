/**
 * Change the font attributes.
 * Style comes from FontBase.
 */

class TermFont
extends TermDisplay
{
    /**
     * What is the style we want?
     */
    int style;

    /**
     * What is the size we want.
     */
    int size;

    /**
     * New term.
     */
    TermFont(int style, int size)
    {
        this.style = style;
        this.size = size;
    }
}

/*
 * $Log$
 * Revision 1.1  1998/02/05 15:47:53  jyh
 * This is a simple term display in an applet.
 *
 */
