/************************************************************************
 * This page displays the result of an output command.
 */

/*
 * Height of the frame.
 */
function FrameHeight()
{
    var height = 100;

    if(self.innerHeight)
        height = self.innerHeight;
    else if(document.documentElement && document.documentElement.clientHeight)
        height = document.documentElement.clientHeight;
    else if(document.body)
        height = document.body.clientHeight;
    return height;
}

/*
 * Abort the current execution.
 */
function Abort()
{
    parent.ShowContent();

    /* May need to close this window */
    var abortbutton = parent.GetObject(self, 'abortbutton');
    if(abortbutton.value == 'Abort')
        location.reload();
    return false;
}

/*
 * Load the content.
 */
function LoadOutput()
{
    var outputframe = parent.GetObject(self, 'outputframe');
    outputframe.src = '/output';
}

/*
 * Load the content.
 */
function OnLoad()
{
    var window_height = FrameHeight();
    var outputframe = parent.GetObject(self, 'outputframe');
    outputframe.style.height = (window_height - 50) + 'px';
    setTimeout('LoadOutput ()', 5000);
    document.onmouseup = parent.CancelMenu;
}

