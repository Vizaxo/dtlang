/**

This file contains example code for how closures are implemented. This
file is not yet part of the compilation process, but serves as an
example for how it works.

 */
#include <stdio.h>
#include <stdlib.h>

typedef struct {
        int tag;
        void* data;
} taggedunion;

/**
A closure is a function pointer and a copy of the lexical environment
where the closure was created.
*/
typedef struct {
	void* (*f)(void*, void**);
	void** env;
} closure;

/**
Calling a closure passes the argument and the environment to the
function.
*/
void* __closure_call(closure* f, void* arg) {
return (f->f)(arg, f->env);
}

/**
This is the function for the clousure returned by a. It looks up x in
the environment and returns it.
*/
void* b (void* y, void** env) {
	return (void*)env[0];
}

/**
This is the constant function (\x. \y. x). It is a function of one
argument (x), and it returns a closure where x is bound in the
environment.
*/
void* a (void* x, void** env) {
	void** benv = malloc(sizeof(void*) * 1);
	benv[0] = x;
	closure* ret = malloc(sizeof(closure));

	*ret = (closure){.f=*b, .env=benv};

	return ret;
}

int main() {
	void* env[0];
	int i = 3;
	int j = 7;
	closure* f = &(closure){.f=a, .env=env};
	printf("%d\n", *(int*)__closure_call(__closure_call(f, &i), &j));
}
