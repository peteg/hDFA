#ifndef _QSORT_H_
#define _QSORT_H_

#include <stdlib.h>

typedef int              cmp_t(void *, const void *, const void *);

void dfa_qsort_r(void *a, size_t n, size_t es, void *thunk, cmp_t *cmp);

#endif /* _QSORT_H_ */
