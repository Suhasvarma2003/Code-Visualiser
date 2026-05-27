from flask import Flask, render_template, request, jsonify, Response, stream_with_context
import sys
import io
import traceback
from bdb import Bdb
import os
import inspect
import gc
import requests
import json
import re
import builtins

from collections import deque
import types


def sanitize_traceback_paths(traceback_str, originated_in_user_code=False):
    if not isinstance(traceback_str, str):
        return traceback_str

    lines = traceback_str.splitlines()
    if not lines:
        return traceback_str

    sanitized_lines = []
    if lines:
        sanitized_lines.append(lines[0])

    try:
        current_script_file_path = os.path.abspath(__file__)
    except NameError:
        try:
            current_script_file_path = os.path.abspath(inspect.getfile(inspect.currentframe()))
        except Exception:
            current_script_file_path = "a.py"

    debugger_script_abs = os.path.abspath(os.path.join(os.path.dirname(current_script_file_path), "a.py"))
    python_std_lib_prefix = os.path.abspath(sys.prefix)

    user_code_frames_started = False
    for i in range(1, len(lines)):
        line = lines[i]
        is_file_line = line.strip().startswith('File "')
        current_line_is_user_code_marker = False

        if is_file_line:
            path_match = re.search(r'File "([^"]+)"(, line \d+, in .*)?', line)
            if path_match:
                filepath_raw = path_match.group(1)
                rest_of_line = path_match.group(2) if path_match.group(2) else ""
                filename = os.path.basename(filepath_raw)
                sanitized_filepath_display = f"<Unknown Source ({filename})>"
                if filepath_raw == "<string>":
                    sanitized_filepath_display = "Your Code"
                    current_line_is_user_code_marker = True
                else:
                    try:
                        abs_filepath = os.path.abspath(filepath_raw)
                        if abs_filepath == debugger_script_abs:
                            sanitized_filepath_display = f"<Debugger Internals ({filename})>"
                        elif abs_filepath.startswith(
                                python_std_lib_prefix) or "bdb.py" in filename or "flask" in abs_filepath.lower().replace(
                            "\\", "/"):
                            lib_type = "Python System Library"
                            if "bdb.py" in filename:
                                lib_type = "Python Debugger Library"
                            elif "flask" in abs_filepath.lower().replace("\\", "/"):
                                lib_type = "Flask Internals"
                            sanitized_filepath_display = f"<{lib_type} ({filename})>"
                        else:
                            sanitized_filepath_display = f"<External Code ({filename})>"
                    except Exception:
                        sanitized_filepath_display = f"<External Code ({filename})> (Path Error)"
                line = f'  File "{sanitized_filepath_display}"{rest_of_line}'

        if originated_in_user_code:
            if current_line_is_user_code_marker: user_code_frames_started = True
            if user_code_frames_started: sanitized_lines.append(line)
        else:
            sanitized_lines.append(line)

    if originated_in_user_code and not user_code_frames_started and len(lines) > 1:
        return sanitize_traceback_paths(traceback_str, False)
    return "\n".join(sanitized_lines)


try:
    app_name = __name__
except NameError:
    app_name = 'web_debugger_app'
app = Flask(app_name, static_folder='static', static_url_path='/static')


class WaitingForInputException(Exception):
    def __init__(self, prompt):
        self.prompt = prompt
        super().__init__(f"Waiting for input: {prompt}")


class WebDebugger(Bdb):
    def __init__(self):
        Bdb.__init__(self)
        self.skip_globals_list = {'__builtins__', 'app', 'Flask', 'Bdb', 'WebDebugger', 'request', 'jsonify',
                                  'render_template', 'gc', 'deque', 'types', 'os', 'sys', 'io', 'traceback', 'inspect',
                                  'requests', 'json', 're', 'remove_think_tag', 'convert_to_python', 'Response',
                                  'stream_with_context', 'time',
                                  'clean_code_response', 'ast', 'sanitize_traceback_paths', 'WaitingForInputException',
                                  'builtins'}
        self.call_id_counter = 0
        self.call_event_log = []
        self.active_call_ids_stack = []
        self.logged_call_ids_stack = []

        self.debugger_internal_methods = {
            'run_debugger', 'user_line', 'user_call', 'user_return',
            '_safe_repr', 'extract_visualizables', '_is_visualizable_candidate',
            '_get_frame_args_and_values', '_custom_input_handler', '_one_time_input_mock',
            'reset_internal_debugger_state',
            'run', 'runcall', 'main',
            'dispatch_line', 'dispatch_call', 'dispatch_return', 'dispatch_exception',
            'stop_here', 'break_here', 'break_anywhere',
        }
        try:
            self.debugger_script_abs_path = os.path.abspath(inspect.getfile(WebDebugger))
        except TypeError:
            self.debugger_script_abs_path = os.path.abspath(__file__ if '__file__' in globals() else "a.py")

        self.python_std_lib_prefix = os.path.abspath(sys.prefix)
        self.reset_internal_debugger_state()
        print("[WebDebugger] Initialized")

    def reset_internal_debugger_state(self):
        self.execution_trace = []
        self.current_step = 0
        self.stdout_buffer = io.StringIO()
        self.original_stdout = sys.stdout
        self.original_builtins_input = None
        self.finished = False
        self.code_lines = []

        self.provided_input_value_for_next_call = None
        self.all_provided_inputs = []
        self.next_input_index = 0

        self.call_id_counter = 0
        self.call_event_log = []
        self.active_call_ids_stack = []
        self.logged_call_ids_stack = []
        Bdb.reset(self)

    def _custom_input_handler(self, prompt=""):
        self.stdout_buffer.write(prompt)
        self.stdout_buffer.flush()
        raise WaitingForInputException(prompt)

    def _one_time_input_mock(self, prompt=""):
        if self.next_input_index < len(self.all_provided_inputs):
            val_to_return = self.all_provided_inputs[self.next_input_index]
            self.stdout_buffer.write(prompt)
            self.stdout_buffer.write(val_to_return + '\n')
            self.stdout_buffer.flush()
            self.next_input_index += 1
            return val_to_return

        if self.provided_input_value_for_next_call is not None:
            val_to_return = self.provided_input_value_for_next_call
            self.provided_input_value_for_next_call = None
            self.stdout_buffer.write(prompt)
            self.stdout_buffer.write(val_to_return + '\n')
            self.stdout_buffer.flush()
            self.all_provided_inputs.append(val_to_return)
            self.next_input_index = len(self.all_provided_inputs)
            return val_to_return

        return self._custom_input_handler(prompt)

    def _safe_repr(self, obj, max_len=150, context_id=None, tracked_ids=None):
        tracked_ids = tracked_ids or set()
        try:
            obj_id = id(obj)
        except TypeError:
            obj_id = None

        if obj_id is not None and obj_id != context_id and obj_id in tracked_ids:
            try:
                obj_type_name = type(obj).__name__
                if isinstance(obj, (list, tuple, dict, deque, set)):
                    try:
                        length = len(obj)
                    except Exception:
                        length = '?'
                    obj_type_name = f"{obj_type_name}[{length}]"
            except Exception:
                obj_type_name = "object"
            return f'<span class="ref-indicator" data-ref-id="{obj_id}" title="Ref to {obj_type_name} @ {hex(obj_id)}">➔ {obj_type_name}</span>'

        if isinstance(obj, (int, float, bool, type(None), complex)): return repr(obj)
        if isinstance(obj, str): s = obj[:max_len] + '...' if len(obj) > max_len else obj; return repr(s)
        if isinstance(obj, bytes): b = obj[:max_len] + b'...' if len(obj) > max_len else obj; return repr(b)

        preview_limit = 3;
        nested_max_len = 25
        if isinstance(obj, (list, tuple, deque)):
            container, prefix, suffix = (['[', ']'], '', '') if not isinstance(obj, deque) else (
                ['[', ']'], 'deque(', ')')
            if isinstance(obj, tuple): container = ('(', ')')
            if not obj: return prefix + container[0] + container[1] + suffix
            items_repr = [self._safe_repr(item, nested_max_len, context_id, tracked_ids) for i, item in
                          enumerate(list(obj)) if i < preview_limit]
            ellipsis = f", ... ({len(obj)})" if len(obj) > preview_limit else ""
            single_tuple_comma = ',' if isinstance(obj, tuple) and len(obj) == 1 else ''
            return f"{prefix}{container[0]}{', '.join(items_repr)}{single_tuple_comma}{ellipsis}{container[1]}{suffix}"
        elif isinstance(obj, set):
            if not obj: return "set()"
            try:
                items_to_preview = sorted(list(obj), key=lambda x: str(type(x)) + repr(x))
            except TypeError:
                items_to_preview = list(obj)
            items_repr = [self._safe_repr(item, nested_max_len, context_id, tracked_ids) for i, item in
                          enumerate(items_to_preview) if i < preview_limit]
            ellipsis = f", ... ({len(obj)})" if len(obj) > preview_limit else ""
            return f"{{{', '.join(items_repr)}{ellipsis}}}"
        elif isinstance(obj, dict):
            if not obj: return "{}"
            items_repr = [
                f"{self._safe_repr(k, max_len=15, context_id=context_id, tracked_ids=tracked_ids)}: {self._safe_repr(v, nested_max_len, context_id, tracked_ids)}"
                for i, (k, v) in enumerate(obj.items()) if i < preview_limit]
            ellipsis = f", ... ({len(obj)})" if len(obj) > preview_limit else ""
            return f"{{{', '.join(items_repr)}{ellipsis}}}"
        try:
            r = repr(obj)
        except Exception:
            r = f"<{type(obj).__name__} (repr error)>"
        return r[:max_len] + '...' if len(r) > max_len else r

    def _is_visualizable_candidate(self, value):
        val_type = type(value)
        if val_type in (list, tuple, dict, deque, set): return True
        if val_type in (int, float, str, bool, bytes, bytearray, complex, type(None), range, types.FunctionType,
                        types.BuiltinFunctionType, types.MethodType, types.ModuleType, type): return False
        if inspect.isclass(value) or inspect.ismodule(value) or inspect.isbuiltin(value) or inspect.isroutine(
                value): return False
        try:
            module_name = val_type.__module__
            if module_name.startswith(('builtins', '__builtin__', 'io.', 'os.', 'sys.', 're.', 'json.', 'datetime.',
                                       'math.', 'socket.', 'threading.', 'queue.', 'abc.')): return False
        except AttributeError:
            pass
        except Exception:
            pass
        return True

    def extract_visualizables(self, variables):
        object_info_map = {};
        queue_bfs = deque();
        visited_for_bfs_ids = set()
        MAX_TRAVERSAL_ITEMS = 500;
        MAX_COLLECTION_ITEMS_TRAVERSE = 30;
        items_processed_bfs = 0
        for var_name, var_value in variables.items():
            if var_name.startswith('__') or not self._is_visualizable_candidate(var_value): continue
            try:
                item_id = id(var_value)
            except TypeError:
                continue

            if item_id not in object_info_map:
                viz_type = 'object'
                if isinstance(var_value, (list, tuple)):
                    viz_type = 'array'
                elif isinstance(var_value, dict):
                    viz_type = 'dict'
                elif type(var_value).__name__ == 'ndarray' and type(var_value).__module__ == 'numpy':
                    viz_type = 'numpy_array'
                elif isinstance(var_value, deque):
                    viz_type = 'deque'
                elif isinstance(var_value, set):
                    viz_type = 'set'
                object_info_map[item_id] = {'item': var_value, 'names': {var_name}, 'vizType': viz_type,
                                            'is_direct': True, 'visited_bfs': False}
                if item_id not in visited_for_bfs_ids: queue_bfs.append(var_value); visited_for_bfs_ids.add(item_id)
            else:
                object_info_map[item_id]['names'].add(var_name)
                object_info_map[item_id]['is_direct'] = True
        while queue_bfs and items_processed_bfs < MAX_TRAVERSAL_ITEMS:
            current_obj = queue_bfs.popleft();
            current_obj_id = id(current_obj);
            items_processed_bfs += 1
            if current_obj_id not in object_info_map: continue
            obj_data = object_info_map[current_obj_id]
            if obj_data['visited_bfs']: continue
            obj_data['visited_bfs'] = True;
            children_to_check = {}
            if obj_data['vizType'] == 'object':
                try:
                    attrs = {};
                    if hasattr(current_obj, '__dict__'): attrs.update(vars(current_obj))
                    if hasattr(current_obj, '__slots__'):
                        for slot in current_obj.__slots__:
                            try:
                                attrs[slot] = getattr(current_obj, slot)
                            except AttributeError:
                                attrs[slot] = '<slot inaccessible>'
                    children_to_check = attrs
                except Exception:
                    pass
            elif obj_data['vizType'] in ('array', 'deque'):
                try:
                    for i, element in enumerate(current_obj):
                        if i >= MAX_COLLECTION_ITEMS_TRAVERSE: break
                        children_to_check[f'_arr_elem_{i}'] = element
                except Exception:
                    pass
            elif obj_data['vizType'] == 'dict':
                try:
                    for i, (key, value) in enumerate(current_obj.items()):
                        if i >= MAX_COLLECTION_ITEMS_TRAVERSE: break
                        if self._is_visualizable_candidate(key):
                            children_to_check[f'_dict_KEY_{i}'] = key
                        if self._is_visualizable_candidate(value):
                            children_to_check[f'_dict_VAL_{i}'] = value
                except Exception:
                    pass
            elif obj_data['vizType'] == 'set':
                try:
                    for i, element_in_set in enumerate(current_obj):
                        if i >= MAX_COLLECTION_ITEMS_TRAVERSE: break
                        children_to_check[f'_set_elem_{i}'] = element_in_set
                except Exception:
                    pass
            for _, child_value in children_to_check.items():
                if not self._is_visualizable_candidate(child_value): continue
                try:
                    child_id = id(child_value)
                except TypeError:
                    continue
                if child_id not in object_info_map:
                    child_viz_type = 'object'
                    if isinstance(child_value, (list, tuple)):
                        child_viz_type = 'array'
                    elif isinstance(child_value, dict):
                        child_viz_type = 'dict'
                    elif type(child_value).__name__ == 'ndarray' and type(child_value).__module__ == 'numpy':
                        child_viz_type = 'numpy_array'
                    elif isinstance(child_value, deque):
                        child_viz_type = 'deque'
                    elif isinstance(child_value, set):
                        child_viz_type = 'set'
                    object_info_map[child_id] = {'item': child_value, 'names': set(), 'vizType': child_viz_type,
                                                 'is_direct': False, 'visited_bfs': False}
                if child_id not in visited_for_bfs_ids: queue_bfs.append(child_value); visited_for_bfs_ids.add(child_id)

        visualizables_to_display = [];
        all_visualized_ids = set(object_info_map.keys())
        for item_id_numeric, obj_data_dict in object_info_map.items():
            item_obj = obj_data_dict['item']
            display_name_parts = sorted(list(obj_data_dict['names']))
            final_display_name = ', '.join(
                display_name_parts) if display_name_parts else f"<{obj_data_dict['vizType']} @ {hex(item_id_numeric)}>"
            item_info = {'vizType': obj_data_dict['vizType'], 'id': item_id_numeric, 'name': final_display_name,
                         'type': type(item_obj).__name__, 'memory_address': f"0x{item_id_numeric:x}",
                         'has_direct_reference': obj_data_dict['is_direct'], 'references': []}
            try:
                if item_info['vizType'] == 'object':
                    item_info['fields'] = [];
                    obj_vars_inspect = {}
                    try:
                        if hasattr(item_obj, '__dict__'): obj_vars_inspect.update(vars(item_obj))
                        if hasattr(item_obj, '__slots__'):
                            for slot in item_obj.__slots__:
                                try:
                                    obj_vars_inspect[slot] = getattr(item_obj, slot)
                                except AttributeError:
                                    obj_vars_inspect[slot] = '<slot inaccessible>'
                    except Exception:
                        obj_vars_inspect = {'<error>': 'Cannot inspect'}
                    for field_name, field_value in obj_vars_inspect.items():
                        if field_name.startswith('__'): continue
                        field_value_repr = self._safe_repr(field_value, context_id=item_id_numeric,
                                                           tracked_ids=all_visualized_ids)
                        item_info['fields'].append(
                            {'name': field_name, 'value': field_value_repr, 'type': type(field_value).__name__})
                        try:
                            field_value_id = id(field_value)
                        except TypeError:
                            field_value_id = None
                        if field_value_id is not None and field_value_id in all_visualized_ids: item_info[
                            'references'].append({'field_name': field_name, 'target_id': field_value_id,
                                                  'target_type': object_info_map[field_value_id]['vizType']})
                elif item_info['vizType'] in ('array', 'deque'):
                    item_info['elements'] = [];
                    item_idx = 0;
                    item_len = 0
                    try:
                        for element in item_obj:
                            item_len += 1;
                            element_repr = self._safe_repr(element, context_id=item_id_numeric,
                                                           tracked_ids=all_visualized_ids)
                            item_info['elements'].append({'index': item_idx, 'value_repr': element_repr})
                            try:
                                element_id = id(element)
                            except TypeError:
                                element_id = None
                            if element_id is not None and element_id in all_visualized_ids: item_info[
                                'references'].append({'field_name': f'[{item_idx}]', 'target_id': element_id,
                                                      'target_type': object_info_map[element_id]['vizType']})
                            item_idx += 1
                        item_info['length'] = item_len
                    except Exception as e:
                        item_info['elements'] = [{'index': 0, 'value_repr': f'<Error: {self._safe_repr(e)}>'}];
                        item_info['length'] = '?'
                elif item_info['vizType'] == 'dict':
                    item_info['pairs'] = []
                    item_len = 0
                    try:
                        for key, value in item_obj.items():
                            item_len += 1
                            key_repr = self._safe_repr(key, context_id=item_id_numeric, tracked_ids=all_visualized_ids)
                            value_repr = self._safe_repr(value, context_id=item_id_numeric,
                                                         tracked_ids=all_visualized_ids)
                            item_info['pairs'].append({'key_repr': key_repr, 'value_repr': value_repr})

                            try:
                                key_id = id(key)
                            except TypeError:
                                key_id = None
                            if key_id is not None and key_id in all_visualized_ids:
                                ref_label_key = f"key_obj({key_repr[:15]}{'...' if len(key_repr) > 15 else ''})"
                                item_info['references'].append({'field_name': ref_label_key, 'target_id': key_id,
                                                                'target_type': object_info_map[key_id]['vizType']})

                            try:
                                value_id = id(value)
                            except TypeError:
                                value_id = None
                            if value_id is not None and value_id in all_visualized_ids:
                                ref_label_val = f"val_for_key({key_repr[:15]}{'...' if len(key_repr) > 15 else ''})"
                                item_info['references'].append({'field_name': ref_label_val, 'target_id': value_id,
                                                                'target_type': object_info_map[value_id]['vizType']})
                        item_info['length'] = item_len
                    except Exception as e:
                        item_info['pairs'] = [{'key_repr': '<Error>', 'value_repr': f'{self._safe_repr(e)}'}];
                        item_info['length'] = '?'
                elif item_info['vizType'] == 'set':
                    item_info['set_elements'] = []
                    item_len = 0
                    try:
                        sorted_elements = []
                        try:
                            sorted_elements = sorted(list(item_obj), key=lambda x: self._safe_repr(x))
                        except TypeError:
                            sorted_elements = list(item_obj)

                        for element in sorted_elements:
                            item_len += 1;
                            element_repr = self._safe_repr(element, context_id=item_id_numeric,
                                                           tracked_ids=all_visualized_ids)
                            item_info['set_elements'].append({'value_repr': element_repr})
                            try:
                                element_id = id(element)
                            except TypeError:
                                element_id = None
                            if element_id is not None and element_id in all_visualized_ids:
                                ref_label = f"elem({element_repr[:20]}{'...' if len(element_repr) > 20 else ''})"
                                item_info['references'].append({'field_name': ref_label, 'target_id': element_id,
                                                                'target_type': object_info_map[element_id]['vizType']})
                        item_info['length'] = item_len
                    except Exception as e:
                        item_info['set_elements'] = [{'value_repr': f'<Error: {self._safe_repr(e)}>'}];
                        item_info['length'] = '?'
                elif item_info['vizType'] == 'numpy_array':
                    item_info['shape'] = self._safe_repr(getattr(item_obj, 'shape', None))
                    item_info['dtype'] = str(getattr(item_obj, 'dtype', 'unknown'))
                    item_info['ndim'] = getattr(item_obj, 'ndim', 'unknown')
                    item_info['size'] = getattr(item_obj, 'size', 'unknown')
                    try:
                        array_str_full = str(item_obj)
                        PREVIEW_MAX_LEN_CHARS = 300
                        PREVIEW_MAX_LINES = 10
                        lines = array_str_full.splitlines()
                        if len(lines) > PREVIEW_MAX_LINES:
                            half_lines = PREVIEW_MAX_LINES // 2
                            array_str_preview = "\n".join(lines[:half_lines]) + "\n...\n" + "\n".join(
                                lines[-half_lines:])
                        else:
                            array_str_preview = array_str_full
                        if len(array_str_preview) > PREVIEW_MAX_LEN_CHARS:
                            array_str_preview = array_str_preview[:PREVIEW_MAX_LEN_CHARS - 3] + "..."
                        item_info['string_preview'] = array_str_preview
                    except Exception as e:
                        item_info['string_preview'] = f"<Error getting str preview: {self._safe_repr(e)}>"
                    if str(getattr(item_obj, 'dtype', '')) == 'object':
                        try:
                            idx_count = 0
                            MAX_OBJ_ELEMENTS_CHECK = 20
                            for element in item_obj.flat:
                                if idx_count >= MAX_OBJ_ELEMENTS_CHECK: break
                                try:
                                    element_id = id(element)
                                    if element_id in all_visualized_ids:
                                        item_info['references'].append({
                                            'field_name': f'[flat_idx_{idx_count}]',
                                            'target_id': element_id,
                                            'target_type': object_info_map[element_id]['vizType']})
                                except TypeError:
                                    pass
                                idx_count += 1
                        except Exception as e_ref:
                            print(f"Error checking references in numpy object array: {e_ref}", file=sys.stderr)
                visualizables_to_display.append(item_info)
            except Exception as e_format:
                print(f"ERROR formatting item for frontend (ID: {item_id_numeric}): {e_format}", file=sys.stderr);
                visualizables_to_display.append({**item_info, 'error': f"Formatting Error: {e_format}"})
        visualizables_to_display.sort(key=lambda x: (not x.get('has_direct_reference', False),
                                                     {'object': 0, 'dict': 1, 'set': 2, 'array': 3, 'numpy_array': 3,
                                                      'deque': 3}.get(
                                                         x.get('vizType'), 4), x.get('name', '')))
        return visualizables_to_display

    def _get_frame_args_and_values(self, frame, tracked_ids_for_repr_context):
        args_info_parts = []
        if not frame or not hasattr(frame, 'f_code') or not hasattr(frame, 'f_locals'): return ""
        ARG_REPR_MAX_LEN = 80;
        VARARGS_ITEM_REPR_MAX_LEN = 30
        co = frame.f_code;
        f_locals = frame.f_locals;
        argcount = co.co_argcount;
        posonlyargcount = getattr(co, 'co_posonlyargcount', 0);
        kwonlyargcount = getattr(co, 'co_kwonlyargcount', 0)
        all_param_names = list(
            co.co_varnames[:co.co_argcount + co.co_kwonlyargcount + getattr(co, 'co_posonlyargcount', 0)])
        for arg_name in all_param_names:
            if arg_name in f_locals:
                value = f_locals[arg_name];
                current_value_repr = "";
                is_special_arg = (arg_name == 'self' or arg_name == 'cls');
                processed_specially = False
                if is_special_arg:
                    try:
                        obj_module_name = None;
                        class_name_str = None;
                        type_description_str = "unknown"
                        if arg_name == 'self':
                            obj_module_name = getattr(value.__class__, '__module__', None)
                            if obj_module_name == '__debugger_run__':
                                class_name_str = value.__class__.__name__;
                                type_description_str = "object"
                        elif arg_name == 'cls':
                            obj_module_name = getattr(value, '__module__', None)
                            if obj_module_name == '__debugger_run__':
                                class_name_str = value.__name__;
                                type_description_str = "class"
                        if class_name_str:
                            custom_repr_base_text = f"< {type_description_str}>";
                            max_len_for_name_part = ARG_REPR_MAX_LEN - len(custom_repr_base_text)
                            if len(class_name_str) <= max_len_for_name_part:
                                current_value_repr = f"<{class_name_str} {type_description_str}>"
                            elif max_len_for_name_part > 3:
                                truncated_class_name = class_name_str[:max_len_for_name_part - 3] + "..."
                                current_value_repr = f"<{truncated_class_name} {type_description_str}>"
                            else:
                                current_value_repr = f"<{type_description_str}>"
                            processed_specially = True
                    except AttributeError:
                        pass
                if not processed_specially: current_value_repr = self._safe_repr(value, max_len=ARG_REPR_MAX_LEN,
                                                                                 context_id=None,
                                                                                 tracked_ids=tracked_ids_for_repr_context)
                args_info_parts.append(f"{arg_name}={current_value_repr}")
        current_arg_idx = co.co_argcount + co.co_kwonlyargcount + getattr(co, 'co_posonlyargcount', 0)
        if co.co_flags & inspect.CO_VARARGS:
            varargs_name = co.co_varnames[current_arg_idx];
            current_arg_idx += 1
            if varargs_name in f_locals:
                varargs_tuple = f_locals[varargs_name]
                if isinstance(varargs_tuple, tuple):
                    args_repr_list = [self._safe_repr(val, max_len=VARARGS_ITEM_REPR_MAX_LEN, context_id=None,
                                                      tracked_ids=tracked_ids_for_repr_context) for val in
                                      varargs_tuple]
                    args_info_parts.append(f"*{varargs_name}=({', '.join(args_repr_list)})")
        if co.co_flags & inspect.CO_VARKEYWORDS:
            varkw_name = co.co_varnames[current_arg_idx]
            if varkw_name in f_locals:
                varkw_dict = f_locals[varkw_name]
                if isinstance(varkw_dict, dict):
                    kwargs_repr_list = [
                        f"{k}={self._safe_repr(v, max_len=VARARGS_ITEM_REPR_MAX_LEN, context_id=None, tracked_ids=tracked_ids_for_repr_context)}"
                        for k, v in varkw_dict.items()]
                    args_info_parts.append(f"**{varkw_name}={{{', '.join(kwargs_repr_list)}}}")
        return ", ".join(args_info_parts)

    def user_call(self, frame, argument_list):
        try:
            function_name = frame.f_code.co_name if frame.f_code.co_name else "<lambda>"
            filename_raw = inspect.getfile(frame)
            try:
                filename_abs = os.path.abspath(filename_raw)
            except Exception:
                filename_abs = filename_raw
            is_debugger_internal_call = (
                    filename_abs == self.debugger_script_abs_path and function_name in self.debugger_internal_methods)
            is_bdb_internal_call = ('bdb.py' in os.path.basename(filename_raw))
            self.call_id_counter += 1;
            new_call_id = self.call_id_counter
            logged_parent_call_id = self.logged_call_ids_stack[-1] if self.logged_call_ids_stack else None
            self.active_call_ids_stack.append(new_call_id)
            if not is_debugger_internal_call and not is_bdb_internal_call:
                args_repr = self._get_frame_args_and_values(frame,
                                                            None) if function_name != "<module>" else "N/A (module scope)"
                line_no_in_function = frame.f_lineno
                self.call_event_log.append(
                    {'type': 'call', 'call_id': new_call_id, 'parent_call_id': logged_parent_call_id,
                     'function_name': function_name, 'args_repr': args_repr, 'line_no_in_function': line_no_in_function,
                     'timestamp_step': self.current_step})
                self.logged_call_ids_stack.append(new_call_id)
        except Exception as e:
            print(f"CRITICAL ERROR in user_call: {e}\n{traceback.format_exc()}", file=sys.stderr)

    def user_return(self, frame, return_value):
        try:
            if not self.active_call_ids_stack: return
            returned_call_id = self.active_call_ids_stack.pop()
            function_name = frame.f_code.co_name if frame.f_code.co_name else "<lambda>"
            filename_raw = inspect.getfile(frame)
            try:
                filename_abs = os.path.abspath(filename_raw)
            except Exception:
                filename_abs = filename_raw
            is_debugger_internal_return = (
                    filename_abs == self.debugger_script_abs_path and function_name in self.debugger_internal_methods)
            is_bdb_internal_return = ('bdb.py' in os.path.basename(filename_raw))
            is_top_level_module_return = False
            corresponding_call_event = next((event for event in reversed(self.call_event_log) if
                                             event['type'] == 'call' and event['call_id'] == returned_call_id), None)
            if corresponding_call_event and corresponding_call_event['function_name'] == '<module>' and \
                    corresponding_call_event['parent_call_id'] is None:
                is_top_level_module_return = True
            if not is_debugger_internal_return and not is_bdb_internal_return and not is_top_level_module_return:
                if self.logged_call_ids_stack and self.logged_call_ids_stack[-1] == returned_call_id:
                    return_value_repr = self._safe_repr(return_value, tracked_ids=None)
                    self.call_event_log.append(
                        {'type': 'return', 'call_id': returned_call_id, 'return_value_repr': return_value_repr,
                         'timestamp_step': self.current_step})
            if self.logged_call_ids_stack and self.logged_call_ids_stack[-1] == returned_call_id:
                self.logged_call_ids_stack.pop()
        except Exception as e:
            print(f"CRITICAL ERROR in user_return: {e}\n{traceback.format_exc()}", file=sys.stderr)

    def user_line(self, frame):
        try:
            filename = inspect.getfile(frame);
            is_user_code_current_line = (filename == '<string>')
            f_code_obj = frame.f_code;
            func_name_for_filter = f_code_obj.co_name if f_code_obj else '<unknown_func>'
            if filename == self.debugger_script_abs_path and func_name_for_filter in self.debugger_internal_methods: self.set_step(); return
            if 'bdb.py' in os.path.basename(filename): self.set_step(); return
            if not is_user_code_current_line: self.set_step(); return

            locals_dict = dict(frame.f_locals);
            globals_dict = dict(frame.f_globals);
            current_context = {**globals_dict, **locals_dict}
            visualizables_data = self.extract_visualizables(current_context)
            tracked_ids_for_var_repr = set(
                vis['id'] for vis in visualizables_data if 'id' in vis and isinstance(vis['id'], int))
            locals_display = {k: self._safe_repr(v, tracked_ids=tracked_ids_for_var_repr) for k, v in
                              locals_dict.items() if
                              not k.startswith('__') and not self._is_visualizable_candidate(v) and not callable(
                                  v) and not isinstance(v, (types.ModuleType, type))}
            globals_display = {k: self._safe_repr(v, tracked_ids=tracked_ids_for_var_repr) for k, v in
                               globals_dict.items() if
                               k not in locals_dict and k not in self.skip_globals_list and not k.startswith(
                                   '__') and not self._is_visualizable_candidate(v) and not callable(
                                   v) and not isinstance(v, (types.ModuleType, type))}
            line_no = frame.f_lineno;
            current_line_content = self.code_lines[line_no - 1].strip() if self.code_lines and 0 <= line_no - 1 < len(
                self.code_lines) else ""
            current_frames_list = [];
            f_iter = frame;
            depth = 0;
            MAX_STACK_DEPTH_DISPLAY_SIMPLE = 7
            while f_iter and depth < MAX_STACK_DEPTH_DISPLAY_SIMPLE:
                try:
                    f_filename_raw_for_stack = inspect.getfile(f_iter)
                    f_name_for_stack = f_iter.f_code.co_name if f_iter.f_code.co_name else '<lambda>'
                    if (
                            f_filename_raw_for_stack == self.debugger_script_abs_path and f_name_for_stack in self.debugger_internal_methods) or \
                            ('bdb.py' in os.path.basename(f_filename_raw_for_stack)):
                        if f_iter.f_back is None: break
                        f_iter = f_iter.f_back;
                        depth += 1;
                        continue
                    if f_filename_raw_for_stack == '<string>':
                        arguments_str = self._get_frame_args_and_values(f_iter, tracked_ids_for_var_repr)
                        display_f_name = f_name_for_stack
                        if f_name_for_stack == '<module>':
                            display_f_name = '(Global Scope)'
                        elif f_name_for_stack == '<lambda>':
                            display_f_name = 'lambda'
                        current_frames_list.append(
                            {'function': display_f_name, 'line': f_iter.f_lineno, 'arguments': arguments_str})
                except Exception as e_stack_build:
                    print(f"Simple stack frame processing error: {e_stack_build}", file=sys.stderr)
                if f_iter.f_back is None: break
                f_iter = f_iter.f_back;
                depth += 1
            sys.stdout.flush();
            current_stdout = self.stdout_buffer.getvalue()
            historical_events_for_this_step = [e for e in self.call_event_log if
                                               e['timestamp_step'] <= self.current_step]
            step_entry = {'step': self.current_step, 'line_no': line_no, 'code': current_line_content,
                          'locals': locals_display, 'globals': globals_display, 'stdout': current_stdout,
                          'visualizables': visualizables_data, 'error': None,
                          'stack_info': {'current_frames': current_frames_list,
                                         'historical_events': historical_events_for_this_step,
                                         'active_call_ids': self.logged_call_ids_stack[:]}}
            self.execution_trace.append(step_entry);
            self.current_step += 1
        except WaitingForInputException:
            raise
        except Exception as e:
            print(f"CRITICAL ERROR in user_line: {e}\n{traceback.format_exc()}", file=sys.stderr)
            raw_error_details = f"Debugger Internal Error in user_line: {e}\n{traceback.format_exc()}";
            sanitized_error_details = sanitize_traceback_paths(raw_error_details, False)
            error_line_no_in_user_line = frame.f_lineno if 'frame' in locals() and hasattr(frame, 'f_lineno') else -1
            error_stack_info = {'current_frames': [], 'historical_events': [e for e in self.call_event_log if
                                                                            e['timestamp_step'] <= self.current_step],
                                'active_call_ids': self.logged_call_ids_stack[:]}
            error_info_user_line = {'step': self.current_step, 'line_no': error_line_no_in_user_line,
                                    'code': "<Debugger Error in user_line>", 'locals': {}, 'globals': {},
                                    'stdout': self.stdout_buffer.getvalue() if hasattr(self, 'stdout_buffer') else "",
                                    'stack_info': error_stack_info, 'visualizables': [],
                                    'error': sanitized_error_details}
            if not self.execution_trace or self.execution_trace[-1].get('error') != error_info_user_line[
                'error']: self.execution_trace.append(error_info_user_line)
            self.current_step += 1;
            self.set_quit()
        finally:
            if not self.quitting: self.set_step()

    def run_debugger(self, code_str, input_to_inject=None, previous_inputs_list=None):
        self.reset_internal_debugger_state()
        self.code_lines = code_str.splitlines()
        self.all_provided_inputs = list(previous_inputs_list) if previous_inputs_list else []
        self.next_input_index = 0
        self.provided_input_value_for_next_call = input_to_inject
        self.stdout_buffer = io.StringIO()
        self.original_stdout = sys.stdout;
        sys.stdout = self.stdout_buffer
        self.original_builtins_input = builtins.input;
        builtins.input = self._one_time_input_mock
        namespace = {"__name__": "__debugger_run__", "deque": deque, "__builtins__": builtins}
        error_occurred = False;
        error_info = None;
        originated_in_user_code_flag = False;
        is_waiting_for_input_flag = False
        try:
            compiled_code = compile(code_str, '<string>', 'exec')
            self.runcall(exec, compiled_code, namespace, namespace)
        except WaitingForInputException as e_input:
            is_waiting_for_input_flag = True
            if self.execution_trace:
                last_step = self.execution_trace[-1]
                last_step['input_request'] = {'prompt': e_input.prompt}
                last_step['stdout'] = self.stdout_buffer.getvalue()
            self.finished = False
        except SyntaxError as e:
            error_occurred = True;
            originated_in_user_code_flag = True
            tb_lines = traceback.format_exception_only(type(e), e);
            error_traceback_raw = "".join(tb_lines)
            final_stack_info = {'current_frames': [], 'historical_events': self.call_event_log[:],
                                'active_call_ids': self.logged_call_ids_stack[:]}
            error_info = {'step': 0, 'line_no': e.lineno or -1,
                          'code': e.text.strip() if hasattr(e, 'text') and e.text else "Syntax Error", 'locals': {},
                          'globals': {}, 'stdout': self.stdout_buffer.getvalue(), 'stack_info': final_stack_info,
                          'visualizables': [],
                          'error': sanitize_traceback_paths(f"SyntaxError: {error_traceback_raw.strip()}",
                                                            originated_in_user_code_flag), '_original_exception': e}
        except Exception as e:
            error_occurred = True;
            exc_type, exc_value, tb = sys.exc_info();
            extracted_tb = traceback.extract_tb(tb)
            originated_in_user_code_flag = bool(extracted_tb and extracted_tb[-1].filename == '<string>')
            error_traceback_raw = "".join(traceback.format_exception(exc_type, exc_value, tb));
            error_line_no = -1
            if extracted_tb and extracted_tb[-1].filename == '<string>': error_line_no = extracted_tb[-1].lineno
            last_step_data = self.execution_trace[-1] if self.execution_trace else {}
            final_error_line = error_line_no if error_line_no != -1 else last_step_data.get('line_no', -1)
            error_current_frames = last_step_data.get('stack_info', {}).get('current_frames', [])
            final_stack_info_on_error = {'current_frames': error_current_frames,
                                         'historical_events': [ev for ev in self.call_event_log if
                                                               ev['timestamp_step'] <= self.current_step],
                                         'active_call_ids': self.logged_call_ids_stack[:]}
            error_info = {'step': self.current_step, 'line_no': final_error_line,
                          'code': last_step_data.get('code', "<Error during execution>"),
                          'locals': last_step_data.get('locals', {}), 'globals': last_step_data.get('globals', {}),
                          'stdout': self.stdout_buffer.getvalue(), 'stack_info': final_stack_info_on_error,
                          'visualizables': last_step_data.get('visualizables', []),
                          'error': sanitize_traceback_paths(error_traceback_raw.strip(), originated_in_user_code_flag),
                          '_original_exception': e}
        finally:
            sys.stdout = self.original_stdout
            if self.original_builtins_input: builtins.input = self.original_builtins_input; self.original_builtins_input = None
            final_stdout_val = self.stdout_buffer.getvalue()
            if not is_waiting_for_input_flag: self.finished = True
            gc.collect();
            final_context_snapshot = dict(namespace)
            try:
                current_final_visualizables = self.extract_visualizables(final_context_snapshot);
                current_tracked_ids_final = set(
                    vis['id'] for vis in current_final_visualizables if 'id' in vis and isinstance(vis['id'], int))
            except Exception as viz_err:
                current_final_visualizables = [
                    {'error': f'Final viz extraction error: {viz_err}'}];
                current_tracked_ids_final = set()
            module_level_vars_display = {k: self._safe_repr(v, tracked_ids=current_tracked_ids_final) for k, v in
                                         final_context_snapshot.items() if
                                         k not in self.skip_globals_list and not k.startswith(
                                             '__') and not self._is_visualizable_candidate(v) and not callable(
                                             v) and not isinstance(v, (types.ModuleType, type))}
            final_historical_events_snapshot = self.call_event_log[:]
            final_active_call_ids_snapshot = self.logged_call_ids_stack[:] if error_occurred else []
            if error_occurred and error_info:
                error_info_for_trace = error_info.copy();
                error_info_for_trace.pop('_original_exception', None);
                error_info_for_trace['stdout'] = final_stdout_val
                error_info_for_trace['stack_info'] = {
                    'current_frames': error_info.get('stack_info', {}).get('current_frames', []),
                    'historical_events': final_historical_events_snapshot,
                    'active_call_ids': final_active_call_ids_snapshot}
                if isinstance(error_info.get('_original_exception'), SyntaxError):
                    error_info_for_trace['locals'] = module_level_vars_display;
                    error_info_for_trace['globals'] = {};
                    error_info_for_trace['visualizables'] = current_final_visualizables
                if not self.execution_trace or self.execution_trace[-1].get('error') != error_info_for_trace['error']:
                    self.execution_trace.append(error_info_for_trace)
                elif self.execution_trace and self.execution_trace[-1].get('error') == error_info_for_trace['error']:
                    self.execution_trace[-1]['stdout'] = final_stdout_val;
                    self.execution_trace[-1]['stack_info'] = error_info_for_trace['stack_info']
                    if isinstance(error_info.get('_original_exception'), SyntaxError):
                        self.execution_trace[-1]['locals'] = module_level_vars_display;
                        self.execution_trace[-1]['globals'] = {};
                        self.execution_trace[-1]['visualizables'] = current_final_visualizables
            elif not is_waiting_for_input_flag:
                final_stack_info_normal_finish = {'current_frames': [],
                                                  'historical_events': final_historical_events_snapshot,
                                                  'active_call_ids': []}
                if self.execution_trace:
                    last_step_ref = self.execution_trace[-1];
                    last_step_ref['stdout'] = final_stdout_val;
                    last_step_ref['visualizables'] = current_final_visualizables;
                    last_step_ref['locals'] = module_level_vars_display;
                    last_step_ref['globals'] = {};
                    last_step_ref['stack_info'] = final_stack_info_normal_finish
                else:
                    self.execution_trace.append(
                        {'step': self.current_step, 'line_no': -1, 'code': 'Finished (No user lines traced)',
                         'locals': module_level_vars_display, 'globals': {}, 'stdout': final_stdout_val,
                         'stack_info': final_stack_info_normal_finish, 'visualizables': current_final_visualizables,
                         'error': None})
        return self.execution_trace


print(f"Flask app '{app.name}' created.")
print(f"Static folder: {os.path.abspath(app.static_folder)}")
print(f"Static URL path: {app.static_url_path}")


def remove_think_tag(text):
    if not isinstance(text, str): return ""
    return re.sub(r'<think>.*?</think>', '', text, flags=re.DOTALL | re.IGNORECASE)


def convert_to_python(code, original_language):
    url = "http://localhost:1234/v1/chat/completions";
    model_name = "local-model"
    system_content = f"""You are an expert code conversion engine. Your sole task is to translate the user-provided code snippet from {original_language} into its equivalent Python code.
**CRITICAL INSTRUCTIONS:**
1.  Output ONLY the raw Python code. 2.  Do NOT include any introductory text. 3.  Do NOT include any explanations or summaries.
4.  Do NOT wrap the code in markdown fences. 5.  Your entire response MUST consist *only* of the valid, executable Python code.
6.  **Do NOT include the `if __name__ == '__main__':` code block.** All code should be at the top level."""
    user_prompt = f"""Convert the following {original_language} code to Python:\n\n```{original_language}\n{code}\n```\nPython code:"""
    payload = {"messages": [{"role": "system", "content": system_content}, {"role": "user", "content": user_prompt}],
               "model": model_name, "temperature": 0.1, "max_tokens": 4000, "stream": False}
    headers = {"Content-Type": "application/json"};
    print(f"--- Sending code conversion request ({original_language} -> Python) ---")
    try:
        response = requests.post(url, headers=headers, data=json.dumps(payload), timeout=90);
        response.raise_for_status();
        result = response.json()
        if "choices" in result and result["choices"] and "message" in result["choices"][0] and "content" in \
                result["choices"][0]["message"]:
            raw_llm_output = result["choices"][0]["message"]["content"];
            print(f"--- RAW LLM Output ---\n```{raw_llm_output}```\n----------------------");
            return raw_llm_output
        else:
            print(f"Error: Unexpected API response structure. Response: {result}",
                  file=sys.stderr);
            return f"Error: Invalid API response. Data: {str(result)[:500]}"
    except requests.exceptions.Timeout:
        print("Error: Code conversion timed out.",
              file=sys.stderr);
        return "Error: Code conversion request timed out (90s)."
    except requests.exceptions.RequestException as e:
        print(f"Error: Code conversion request failed: {e}",
              file=sys.stderr);
        return f"Error: API request failed ({type(e).__name__}). LM Studio running?"
    except Exception as e:
        print(f"Unexpected error during code conversion: {e}\n{traceback.format_exc()}",
              file=sys.stderr);
        return f"Error: Unexpected conversion error ({type(e).__name__})."


def generate_llm_stream(code, user_question):
    url = "http://localhost:1234/v1/chat/completions"
    model_name = "local-model"
    system_prompt = """You are a helpful and insightful AI programming assistant.
The user will provide you with a code snippet and a specific question or doubt they have about that code.
Your task is to analyze the code and provide a clear, concise, and accurate explanation or answer to the user's question, focusing on the provided code.
If the question is unclear or the code is insufficient to answer, politely ask for clarification or more context.
Do not provide general programming advice unless it's directly relevant to the question and code.
Structure your response in a readable way. You can use markdown for formatting if appropriate (e.g., code blocks for small examples, lists).
Keep your response focused and to the point. Avoid overly verbose explanations.
"""
    user_prompt_text = f"""Here is the code:
```python
{code}
```

My question about this code is:
{user_question}

Please provide your insight:"""

    payload = {
        "messages": [
            {"role": "system", "content": system_prompt},
            {"role": "user", "content": user_prompt_text}
        ],
        "model": model_name,
        "temperature": 0.3,
        "max_tokens": 1500,
        "stream": True
    }
    headers = {"Content-Type": "application/json", "Accept": "text/event-stream"}

    try:
        print(f"--- Sending LLM insight stream request ---")
        with requests.post(url, headers=headers, json=payload, stream=True, timeout=120) as r:
            r.raise_for_status()
            for line in r.iter_lines():
                if line:
                    decoded_line = line.decode('utf-8')
                    if decoded_line.startswith('data: '):
                        json_data_str = decoded_line[len('data: '):].strip()
                        if json_data_str == "[DONE]":
                            print("LLM stream [DONE] received.")
                            yield f"data: {json.dumps({'choices': [{'delta': {'content': ''}, 'finish_reason': 'stop'}]})}\n\n"
                            break
                        try:
                            yield f"data: {json_data_str}\n\n"
                        except json.JSONDecodeError:
                            print(f"LLM stream: JSONDecodeError for line: {json_data_str}", file=sys.stderr)
                    elif decoded_line.strip() == ":" or decoded_line.strip().startswith(": ping"):
                        yield ": keep-alive\n\n"
                    elif decoded_line.strip():
                        print(f"LLM stream: Received non-data line: {decoded_line}", file=sys.stderr)

    except requests.exceptions.Timeout:
        print("LLM stream: Request timed out.", file=sys.stderr)
        yield f"data: {json.dumps({'error': 'LLM request timed out (120s)'})}\n\n"
    except requests.exceptions.RequestException as e:
        print(f"LLM stream: Request failed: {e}", file=sys.stderr)
        yield f"data: {json.dumps({'error': f'LLM API request failed ({type(e).__name__})'})}\n\n"
    except Exception as e:
        print(f"LLM stream: Unexpected error: {e}\n{traceback.format_exc()}", file=sys.stderr)
        yield f"data: {json.dumps({'error': f'Unexpected error during LLM stream ({type(e).__name__})'})}\n\n"
    finally:
        print("--- LLM insight stream request finished ---")


def clean_code_response(response_text):
    if not isinstance(response_text, str): print("Warning: Invalid input to clean_code_response.",
                                                 file=sys.stderr); return "Error: Invalid input for cleaning."
    if response_text.strip().startswith("Error:"): return response_text
    cleaned = remove_think_tag(response_text);
    lines = cleaned.splitlines();
    code_start_index = 0;
    found_code = False
    for i, line in enumerate(lines):
        stripped_line = line.strip()
        if not stripped_line: continue
        if stripped_line.startswith(('def ', 'class ', 'import ', 'from ', '#', '"""', "'''")) or \
                re.match(r'^[a-zA-Z_][a-zA-Z0-9_]*\s*=', stripped_line) or \
                re.match(r'^[a-zA-Z_][a-zA-Z0-9_]*\s*\(.*\)\s*:', stripped_line) or \
                re.match(r'^print\(', stripped_line) or \
                re.match(r'^[a-zA-Z_][a-zA-Z0-9_]*\(', stripped_line): code_start_index = i; found_code = True; break
    if found_code: cleaned = "\n".join(lines[code_start_index:])
    cleaned = re.sub(r'^\s*```(python|py)?\s*\n', '', cleaned, flags=re.IGNORECASE | re.MULTILINE)
    cleaned = re.sub(r'\n\s*```\s*$', '', cleaned, flags=re.MULTILINE);
    cleaned = cleaned.strip()
    if not cleaned: return "Error: Code cleaning failed (empty). Original might be non-code."
    return cleaned


@app.route('/')
def index(): return render_template('index.html')


debugger_instance = WebDebugger()


@app.route('/debug', methods=['POST'])
def debug():
    global debugger_instance
    if not request.is_json: return jsonify({"error": "Request must be JSON"}), 400
    data = request.get_json();
    if not data: return jsonify({"error": "No JSON data received"}), 400
    code = data.get('code', '');
    language = data.get('language', 'Python')
    injected_input = data.get('injected_input', None)
    all_previous_inputs = data.get('all_previous_inputs', [])
    is_continuation = data.get('is_continuation', False)
    execution_trace = [];
    debugger_actually_finished = False;
    error_message = None
    final_code_to_debug = code
    if not is_continuation:
        debugger_instance.reset_internal_debugger_state()
        debugger_instance.all_provided_inputs = []
        debugger_instance.next_input_index = 0
        print("[Debug Route] New run: Global debugger_instance fully reset.")
    else:
        print(
            f"[Debug Route] Continuation: Using existing debugger_instance. All previous inputs count: {len(debugger_instance.all_provided_inputs)}")
    try:
        if language != "Python" and not is_continuation:
            converted_code_raw = convert_to_python(code, language)
            if converted_code_raw.startswith("Error:"): raise ValueError(converted_code_raw)
            final_code_to_debug = clean_code_response(converted_code_raw)
            if final_code_to_debug.startswith("Error:") or not final_code_to_debug.strip():
                error_msg = final_code_to_debug if final_code_to_debug.startswith(
                    "Error:") else "Conversion resulted in empty code."
                if "empty code" in error_msg: error_msg += f" Raw: '{converted_code_raw[:100]}...'"
                raise ValueError(error_msg)
        elif not is_continuation:
            pass
        else:
            final_code_to_debug = "\n".join(debugger_instance.code_lines) if debugger_instance.code_lines else code
            print(
                f"[Debug Route] Continuation: Using code from debugger_instance (length {len(debugger_instance.code_lines)} lines)")
        if not final_code_to_debug or not final_code_to_debug.strip(): raise ValueError("No Python code to debug.")
        current_all_inputs_for_run = list(debugger_instance.all_provided_inputs)
        print(
            f"[Debug Route] Calling run_debugger. Injected: {injected_input is not None}. Prev inputs for this run: {len(current_all_inputs_for_run)}")
        execution_trace = debugger_instance.run_debugger(final_code_to_debug, input_to_inject=injected_input,
                                                         previous_inputs_list=current_all_inputs_for_run)
        is_waiting_for_input = bool(execution_trace and execution_trace[-1].get('input_request'))
        debugger_actually_finished = debugger_instance.finished and not is_waiting_for_input
        if execution_trace and execution_trace[-1].get('error'):
            error_message = execution_trace[-1]['error']
        elif len(execution_trace) == 1 and execution_trace[0].get('error'):
            error_message = execution_trace[0]['error']
    except ValueError as ve:
        error_message = str(ve);
        debugger_actually_finished = True
        if not execution_trace or not any(step.get('error') == error_message for step in execution_trace):
            execution_trace = [
                {'step': 0, 'line_no': -1, 'code': 'Error Setup/Conversion', 'locals': {}, 'globals': {}, 'stdout': '',
                 'stack_info': {'current_frames': [], 'historical_events': [], 'active_call_ids': []},
                 'visualizables': [], 'error': error_message}]
    except Exception as e:
        raw_internal_error_tb = f"Internal server error during debugging: {traceback.format_exc()}"
        error_message = sanitize_traceback_paths(raw_internal_error_tb, False);
        debugger_actually_finished = True
        if not execution_trace or not any(step.get('error') == error_message for step in execution_trace):
            execution_trace = [
                {'step': 0, 'line_no': -1, 'code': 'Internal Server Error', 'locals': {}, 'globals': {}, 'stdout': '',
                 'stack_info': {'current_frames': [], 'historical_events': [], 'active_call_ids': []},
                 'visualizables': [], 'error': error_message}]
    if not isinstance(execution_trace, list):
        execution_trace = [];
        error_message = sanitize_traceback_paths(error_message or "Internal error: Trace invalid.", False);
        debugger_actually_finished = True
    if error_message and (not execution_trace or not any(step.get('error') for step in execution_trace)):
        execution_trace = [
            {'step': 0, 'line_no': -1, 'code': 'Error Occurred', 'stdout': '', 'locals': {}, 'globals': {},
             'stack_info': {'current_frames': [], 'historical_events': [], 'active_call_ids': []}, 'visualizables': [],
             'error': error_message}]
    print(
        f"[Debug Route] Response: Finished: {debugger_actually_finished}, Error: {error_message is not None}, Trace len: {len(execution_trace)}, Updated inputs len: {len(debugger_instance.all_provided_inputs)}")
    return jsonify({'trace': execution_trace, 'finished': debugger_actually_finished, 'error': error_message,
                    'updated_all_inputs': debugger_instance.all_provided_inputs})


@app.route('/ask_llm')
def ask_llm_stream():
    code = request.args.get('code', '')
    user_question = request.args.get('question', '')

    if not code.strip():
        def error_stream_code():
            yield f"data: {json.dumps({'error': 'Code cannot be empty.'})}\n\n"

        return Response(stream_with_context(error_stream_code()), mimetype='text/event-stream')

    if not user_question.strip():
        def error_stream_question():
            yield f"data: {json.dumps({'error': 'Question cannot be empty.'})}\n\n"

        return Response(stream_with_context(error_stream_question()), mimetype='text/event-stream')

    return Response(stream_with_context(generate_llm_stream(code, user_question)), mimetype='text/event-stream')


if __name__ == '__main__':
    print("--- Starting Flask Server ---");
    print("Access at: http://127.0.0.1:50000");
    print("---------------------------")
    app.run(host='0.0.0.0', port=50000, debug=True)