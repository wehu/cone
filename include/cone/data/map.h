#pragma once

#include "cone/builtins.h"

namespace cone {
  namespace data {
    namespace map {
      const std::function<object_t(const cont_t &, stack_t, effects_t)> cone__empty = 
      [=](const cont_t &k, stack_t stack, effects_t effs) {
        return k(py::object(py::module_::import("immutables").attr("Map")()));
      };

      const std::function<object_t(const cont_t &, stack_t, effects_t, const object_t &)> cone__first = 
      [=](const cont_t &k, stack_t stack, effects_t effs, const object_t &m) {
        return k(py::reinterpret_borrow<py::object>(*____to_py_object(m).begin()));
      };
  
      const std::function<object_t(const cont_t &, stack_t, effects_t, const object_t &, const object_t &)> cone__get = 
      [=](const cont_t &k, stack_t stack, effects_t effs, const object_t &m, const object_t &key) {
        return k(py::object(____to_py_object(m).attr("get")(____to_py_object(key))));
      };
  
      const std::function<object_t(const cont_t &, stack_t, effects_t, const object_t &, const object_t &, const object_t &)> cone__set = 
      [=](const cont_t &k, stack_t stack, effects_t effs, const object_t &m, const object_t &key, const object_t &v) {
        return k(py::object(____to_py_object(m).attr("set")(____to_py_object(key), ____to_py_object(v))));
      };
  
      const std::function<object_t(const cont_t &, stack_t, effects_t, const object_t &, const object_t &)> cone__del = 
      [=](const cont_t &k, stack_t stack, effects_t effs, const object_t &m, const object_t &key) {
        return k(py::object(____to_py_object(m).attr("delete")(____to_py_object(key))));
      };
  
    }
  }
}