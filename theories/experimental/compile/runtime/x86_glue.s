/*
 * Glue functions for X86 code.
 *
 * Exit function gets an argument in %ebx,
 * and it returns that value to the caller function.
 */

/*
 * Temporary spill area.
 */
	.text
	.align	4
	.global	__exit

	/* __exit is a closure */
__exit:
	movl	%ebx,%eax
	popl	%ebp
	popl	%edi
	popl	%esi
	popl	%edx
	popl	%ecx
	popl	%ebx
	ret

/*
 * Wrapper for the main function.
 * Main has 3 arguments: a continuation, an exception
 * handler, and argv.
 */
	.global	__main
__main:
	pushl	%ebx
	pushl	%ecx
	pushl	%edx
	pushl	%esi
	pushl	%edi
	pushl	%ebp
	movl	28(%esp),%eax
	movl	32(%esp),%ebx
	movl	$__m_spills,%ebp
	jmp	__m_main

/*
 * Garbage collector pushes all the registers,
 * and the address of the calling function.
 */
	.global __gc
__gc:
	pushl	%ebp
	pushl	%edi
	pushl	%esi
	pushl	%edx
	pushl	%ecx
	pushl	%ebx
	pushl	%eax
	pushl	%esp
	call	gc
	addl	$4,%esp
	popl	%eax
	popl	%ebx
	popl	%ecx
	popl	%edx
	popl	%esi
	popl	%edi
	popl	%ebp
	ret
