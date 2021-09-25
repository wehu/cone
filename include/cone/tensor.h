#pragma once

#include "cone/builtins.h"

namespace cone {
  namespace data {
    namespace tensor {
      const std::function<object(const cont &, states, effects, const object &)> cone__full = 
      [=](const cont &k, states state, effects effs, const object &elem) {
        auto typeargs = ____to_py_object(state->back()[____typeargs]);
        auto shape = py::cast<py::list>(typeargs)[0];
        return k(py::object(py::module_::import("numpy").attr("full")(shape, ____to_py_object(elem))));
      };
  
      const std::function<object(const cont &, states, effects, const object &, const object &)> cone__matmul = 
      [=](const cont &k, states state, effects effs, const object &lhs, const object &rhs) {
        return k(py::object(py::module_::import("numpy").attr("matmul")(____to_py_object(lhs), ____to_py_object(rhs))));
      };
  
      const std::function<object(const cont &, states, effects, const object &, const object &)> cone__convolve_full = 
      [=](const cont &k, states state, effects effs, const object &lhs, const object &rhs) {
        return k(py::object(py::module_::import("numpy").attr("convolve")(____to_py_object(lhs), ____to_py_object(rhs))));
      };
  
      const std::function<object(const cont &, states, effects, const object &, const object &)> cone__convolve_same = 
      [=](const cont &k, states state, effects effs, const object &lhs, const object &rhs) {
        return k(py::object(py::module_::import("numpy").attr("convolve")(____to_py_object(lhs), ____to_py_object(rhs), py::str("same"))));
      };
  
      const std::function<object(const cont &, states, effects, const object &, const object &)> cone__convolve_valid = 
      [=](const cont &k, states state, effects effs, const object &lhs, const object &rhs) {
        return k(py::object(py::module_::import("numpy").attr("convolve")(____to_py_object(lhs), ____to_py_object(rhs), py::str("valid"))));
      };
  
    }
  }
}