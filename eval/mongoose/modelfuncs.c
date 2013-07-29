
#include <pthread.h>

void 
_pthread_cleanup_push_defer_model(struct _pthread_cleanup_buffer *__buffer,
				  void (*__routine) (void *), void *__arg)
{
        __buffer->__routine = __routine;
        __buffer->__arg = __arg;
}

void 
_pthread_cleanup_pop_restore_model(struct _pthread_cleanup_buffer *__buffer,
				   int __execute)
{
        if (__execute)
                __buffer->__routine(__buffer->__arg);
}
