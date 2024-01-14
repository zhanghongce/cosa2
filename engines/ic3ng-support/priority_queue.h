#pragma once

#include "model.h"
#include "lemma.h"

#include <algorithm>
#include <queue>

namespace pono {

// structure for fidx, cex
struct fcex_t{
  unsigned fidx;
  Model * cex;
  const fcex_t * next;
  LCexOrigin cex_origin;
  fcex_t(unsigned fidx_, Model * cex_,  LCexOrigin origin, const fcex_t * n) : 
    fidx(fidx_), cex(cex_), cex_origin(origin), next(n) {}
};
// comparison for priority queue
// since priority queue returns largest element, we swap the arguments
// -- we want the lowest index to be processed first
struct fcex_t_ordering {
  bool operator()(const fcex_t * a, const fcex_t * b) {
    return b->fidx < a->fidx; }
};

// will need to be cleared every time finishing recursive_block
class Ic3PriorityQueue {
public:
  ~Ic3PriorityQueue() { clear(); }

  void new_proof_goal(unsigned fidx_, Model * cex_,  LCexOrigin origin,
                      const fcex_t * n = NULL) {
    fcex_t * pg = new fcex_t(fidx_, cex_, origin, n);
    queue_.push(pg);
    store_.push_back(pg);
  }

  fcex_t * top() { return queue_.top(); }
  void pop() { queue_.pop(); } // pop the top one
  bool empty() const { return queue_.empty(); }
  void clear() {
    for (auto p : store_) {
      delete p;
    }
    store_.clear();
    while (!queue_.empty()) {
      queue_.pop();
    }
  }

protected:
  std::priority_queue<fcex_t *, std::vector<fcex_t *>, fcex_t_ordering>
      queue_;
  std::vector<fcex_t *> store_;
};

} // pono
