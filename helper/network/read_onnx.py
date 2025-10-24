from beartype import beartype
import onnxruntime as ort
import numpy as np
import traceback
import warnings
import torch
import onnx
import io

from ..data.onnx_error import *
from . import onnx2pytorch

custom_quirks = {
    'Reshape': {
        'fix_batch_size': False
    },
    'Transpose': {
        'merge_batch_size_with_channel': True,
        'remove_gdvb_transpose': True,
    },
    'Softmax' :{
        'skip_last_layer': True
    },
    'Squeeze' :{
        'skip_last_layer': True
    },
    'Conv' :{
        'merge_batch_norm': True
    },
}

@beartype
def _load_onnx(path: str | io.BytesIO):
    if isinstance(path, str):
        onnx_model = onnx.load(path)
    else:
        onnx_model = onnx.load_model_from_string(path.getvalue())
    return onnx_model

@beartype
def inference_onnx(path: str | io.BytesIO, *inputs: np.ndarray):
    sess = ort.InferenceSession(_load_onnx(path).SerializeToString())
    names = [i.name for i in sess.get_inputs()]
    return sess.run(None, dict(zip(names, inputs)))


@beartype
def add_batch(shape: tuple) -> tuple:
    if len(shape) == 1:
        return (1, shape[0])
    
    if shape[0] not in [-1, 1]:
        return (1, *shape)
    
    return shape
        

@beartype
def _parse_onnx(path: str | io.BytesIO) -> tuple:
    # load model
    onnx_model = _load_onnx(path)
    
    # extract shapes
    onnx_inputs = [node.name for node in onnx_model.graph.input]
    initializers = [node.name for node in onnx_model.graph.initializer]
    inputs = list(set(onnx_inputs) - set(initializers))
    inputs = [node for node in onnx_model.graph.input if node.name in inputs]

    onnx_input_dims = inputs[0].type.tensor_type.shape.dim
    onnx_output_dims = onnx_model.graph.output[0].type.tensor_type.shape.dim
    
    orig_input_shape = tuple(d.dim_value if d.dim_value > 0 else 1 for d in onnx_input_dims)
    orig_output_shape = tuple(d.dim_value if d.dim_value > 0 else 1 for d in onnx_output_dims) if len(onnx_output_dims) else (1,)
    
    batched_input_shape = add_batch(orig_input_shape)
    batched_output_shape = add_batch(orig_output_shape)

    pytorch_model = onnx2pytorch.ConvertModel(onnx_model, experimental=True, quirks=custom_quirks)
    pytorch_model.eval()
    
    pytorch_model.to(torch.get_default_dtype())
    
    if custom_quirks.get('Softmax', {}).get('skip_last_layer', False):
        custom_quirks['Softmax']['skip_last_layer'] = pytorch_model.is_last_removed.get('Softmax', False)
    
    if custom_quirks.get('Squeeze', {}).get('skip_last_layer', False):
        custom_quirks['Squeeze']['skip_last_layer'] = pytorch_model.is_last_removed.get('Squeeze', False)
    
    # check conversion
    correct_conversion = True
    try:
        batch = 2
        dummy = torch.randn(batch, *batched_input_shape[1:], dtype=torch.get_default_dtype())
        output_onnx = torch.cat([torch.from_numpy(inference_onnx(path, dummy[i].view(orig_input_shape).float().numpy())[0]).view(batched_output_shape) for i in range(batch)])
        output_pytorch = pytorch_model(dummy).detach().numpy()
        correct_conversion = np.allclose(output_pytorch, output_onnx, 1e-5, 1e-5)
    except:
        raise OnnxConversionError

    if not correct_conversion and custom_quirks.get('Conv', {}).get('merge_batch_norm', False):
        raise OnnxMergeBatchNormError
    
    if not correct_conversion and not custom_quirks.get('Softmax', {}).get('skip_last_layer', False):
        raise OnnxOutputAllCloseError
        
    return pytorch_model, batched_input_shape, batched_output_shape


@beartype
def parse_onnx(path: str | io.BytesIO) -> tuple:
    while True:
        try:
            return _parse_onnx(path)
        except OnnxMergeBatchNormError:
            custom_quirks['Conv']['merge_batch_norm'] = False
            continue
        except OnnxOutputAllCloseError:
            # print(f'[{i}] Model was converted incorrectly. Try again.')
            continue
        except OnnxConversionError:
            if not custom_quirks['Reshape']['fix_batch_size']:
                custom_quirks['Reshape']['fix_batch_size'] = True
                continue
            else:
                warnings.warn(f'Unable to convert onnx to pytorch model')
                traceback.print_exc()
                exit()
        except SystemExit:
            exit()
        except:
            warnings.warn(f'Unable to convert onnx to pytorch model')
            traceback.print_exc()
            exit()
            
            