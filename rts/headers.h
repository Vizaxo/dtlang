#ifndef __HEADER_H__
#define __HEADER_H__

//TODO: nicely split .h and .c files, provide nice interface for rts

#include <stdio.h>
#include <stdlib.h>

typedef struct heap_data {
	union {
		int tag;
		struct heap_data* (*f)(struct heap_data* arg, struct heap_data** mem);
	} data;
        //Null-terminated array of heap data (either env or tagged union data)
	struct heap_data** mem;
} heap_data;

typedef struct heap_ptr {
	heap_data** ptr;
	struct heap_ptr* next;
} heap_ptr;

typedef struct alloc_info {
	//char free:1;
	unsigned char marked:1;
	//size_t size;
	struct alloc_info* prev;
} alloc_info;

alloc_info* prev_alloc = NULL;

void mark_heap(heap_data* addr);
void mark_from_roots();
void sweep();
void run_gc();

int allocated = 0;
int deallocated = 0;

void* my_malloc(size_t size) {
	alloc_info* addr = malloc(sizeof(alloc_info) + size);
	allocated++;
	if (addr == NULL) {
		//die("Memory allocation failed!");
		exit(1);
		return NULL;
	}
        addr->marked = 0;
	addr->prev=prev_alloc;
	prev_alloc = addr;
	return addr+1;
}

void mark(heap_data* user_addr) {
	if (user_addr != NULL) {
		alloc_info* addr = ((alloc_info*)user_addr)-1;
		if (addr != NULL) {
			addr->marked = 1;
		}
	}
}

heap_data* heap_alloc(size_t mem_count) {
	run_gc();
	heap_data* data = my_malloc(sizeof(heap_data) + sizeof(alloc_info));
	heap_data** arr = my_malloc(sizeof(heap_data*) * (mem_count+1));
	data->mem = arr;
	data->mem[mem_count] = NULL;
	return data;
}

// Every pointer is a node in a linked list from the root node
heap_ptr root_ptr;
heap_ptr* head_heap_ptr;

void initialise_rts() {
	//TODO: make this list point backwards
	root_ptr = (heap_ptr){NULL, NULL};
	head_heap_ptr = &root_ptr;
}

heap_data* closure_call(heap_data* f, heap_data* arg) {
	// Save the previous head pointer so it can be restored after
	// exiting from the function
	heap_ptr* save_head = head_heap_ptr;
	heap_data* ret = (f->data.f)(arg, f->mem);
	head_heap_ptr = save_head;
	head_heap_ptr->next = NULL;
	return ret;
}

void funcall(void (*f)()) {
	heap_ptr* save_head = head_heap_ptr;
	f();
	head_heap_ptr = save_head;
	head_heap_ptr->next = NULL;
}

void mark_heap(heap_data* addr) {
	if (addr == NULL) return;
	heap_data** d = addr->mem;
	if (d == NULL) return;
	if ((((alloc_info*)addr)-1)->marked)
		return;
	for(; *d != NULL; d++) {
		mark(*d);
		mark_heap(*d);
	}
}

void print_heap_rec(heap_data* addr) {
	if (addr == NULL) return;
	heap_data** d = addr->mem;
	if (d == NULL) return;
	if ((((alloc_info*)addr)-1)->marked)
		return;
	for(; *d != NULL; d++) {
		mark(*d);
		printf("Heap node at %p\n", ((alloc_info*)*(d))-1);
		print_heap_rec(*d);
	}
}

void print_heap_root_nodes() {
	printf("\tRoots\n");
	heap_ptr* curr = &root_ptr;
	while(curr != NULL) {
		if (curr->ptr != NULL) {
			printf("Heap node at %p\n", ((alloc_info*)*(curr->ptr))-1);
			print_heap_rec(*(curr->ptr));
		}
	        curr=curr->next;
	}
	printf("\tFinished\n");
}

void print_heap_alloc_list() {
	printf("\tAlloc list\n");
	alloc_info* next = NULL;
	alloc_info* curr = prev_alloc;
	alloc_info* prev;
	while(curr != NULL) {
		alloc_info* prev = curr->prev;
		printf("Heap node at %p. Marked: %d\n", curr, curr->marked);
		next=curr;
		curr=prev;
	}
	printf("\tFinished\n");
}

void run_gc() {
	//print_heap_root_nodes();
	//print_heap_alloc_list();
	mark_from_roots();
	sweep();
}

void sweep() {
	alloc_info* next = NULL;
	alloc_info* curr = prev_alloc;
	alloc_info* prev;
	while(curr != NULL) {
		alloc_info* prev = curr->prev;
		if (curr->marked) {
			curr->marked = 0;
			next=curr;
		} else {
			if (next != NULL)
				next->prev = curr->prev; //Update the free list
			if (prev_alloc == curr)
				prev_alloc = curr->prev;
			free(curr);
			deallocated++;
		}
		curr=prev;
	}
}

void mark_from_roots() {
	heap_ptr* curr = &root_ptr;
	while(curr != NULL) {
		if (curr->ptr != NULL) {
			mark(*(curr->ptr));
			mark_heap(*(curr->ptr));
		}
	        curr=curr->next;
	}
}

#endif //__HEADER_H__
