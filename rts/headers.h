#ifndef __HEADER_H__
#define __HEADER_H__


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
	heap_data* ptr;
	struct heap_ptr* next;
} heap_ptr;

heap_data* heap_alloc(size_t mem_count) {
	heap_data* data = malloc(sizeof(heap_data));
	if (mem_count == 0) {
		data->mem = NULL;
	} else {
		heap_data** arr = malloc(sizeof(heap_data*) * (mem_count+1));
		data->mem = arr;
		data->mem[mem_count] = NULL;
	}
	return data;
}

// Every pointer is a node in a linked list from the root node
heap_ptr root_ptr = {NULL, NULL};
heap_ptr* head_heap_ptr = &root_ptr;

heap_data* closure_call(heap_data* f, heap_data* arg) {
	// Save the previous head pointer so it can be restored after
	// exiting from the function
	heap_ptr* save_head = head_heap_ptr;
	heap_data* ret = (f->data.f)(arg, f->mem);
	head_heap_ptr = save_head;
	save_head->next = NULL;
	return ret;
}


#endif //__HEADER_H__
