#pragma once

#include "cone/builtins.h"

namespace cone {
  namespace data {
    namespace tensor {
      const std::function<object_t(const cont_t &, stack_t, effects_t, const object_t &, const object_t &)> cone__full = 
      [=](const cont_t &k, stack_t stack, effects_t effs, const object_t &elem, const object_t &dyn_dims) {
        auto typeargs = ____to_py_object(stack->back()[____typeargs]);
        auto shape = py::cast<py::list>(py::cast<py::list>(typeargs)[0]);
        auto rank = py::len(shape);
        for (unsigned i=0; i<rank; ++i) {
          if (py::cast<py::int_>(shape[i]) == -1) {
            throw ____cone_exception("unsupported dynamic shape so far");
          }
        }
        return k(py::object(py::module_::import("numpy").attr("full")(shape, ____to_py_object(elem))));
      };
  
    }
  }
}