#pragma once

#include "cone/builtins.h"

namespace cone {
  namespace data {
    namespace tensor {
      
      const std::function<object_t(const cont_t &, stack_t, effects_t, const object_t &, const object_t &)> cone__full = 
      [=](const cont_t &k, stack_t stack, effects_t effs, const object_t &elem, const object_t &dyn_dims) {
        auto typeargs = py::cast<py::list>(____to_py_object(stack->back()[____typeargs]));
        auto shape = py::cast<py::list>(typeargs[0]);
        auto rank = py::len(shape);
        auto dyns = ____list_to_vector(dyn_dims);
        int dyn_index = 0;
        for (unsigned i=0; i<rank; ++i) {
          if (py::cast<py::int_>(shape[i]) == -1) {
            if (dyn_index >= dyns.size()) {
              throw ____cone_exception("dynamic dims are less then required in shape annotations");
            }
            shape[i] = dyns[dyn_index++];
          }
        }
        if (dyn_index != dyns.size()) {
          throw ____cone_exception("dynamic dims are more than required in shape annotations");
        }
        py::object dtype = py::none();
        if (py::len(typeargs) > 1) {
          dtype = typeargs[1];
        }
        return k(py::object(py::module_::import("numpy").attr("full")(shape, ____to_py_object(elem), py::arg("dtype") = dtype)));
      };
  
    }
  }
}