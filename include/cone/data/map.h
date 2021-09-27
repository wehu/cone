#pragma once

#include "cone/builtins.h"

namespace cone {
  namespace data {
    namespace map {

      const std::function<object_t(const cont_t &, stack_t, effects_t, const object_t &)> cone__first = 
      [=](const cont_t &k, stack_t stack, effects_t effs, const object_t &m) {
        return k(py::reinterpret_borrow<py::object>(*____to_py_object(m).begin()));
      };

    }
  }
}