/* =========================================================================
   1. GEOHASH ENCODING & DECODING BASE ALGORITHMS
   ========================================================================= */
const BASE32 = "0123456789bcdefghjkmnpqrstuvwxyz";
const MAX_RESULT_ITEMS = 5000;

function decodeGeohash(geohash) {
    geohash = geohash.toLowerCase().trim();
    if (!geohash || geohash.length > 12) return null;
    let isEven = true;
    let lat = [-90.0, 90.0];
    let lon = [-180.0, 180.0];

    for (let i = 0; i < geohash.length; i++) {
        const c = geohash.charAt(i);
        const cd = BASE32.indexOf(c);
        if (cd === -1) return null;

        for (let j = 4; j >= 0; j--) {
            const bit = (cd >> j) & 1;
            if (isEven) {
                const mid = (lon[0] + lon[1]) / 2;
                if (bit === 1) lon[0] = mid; else lon[1] = mid;
            } else {
                const mid = (lat[0] + lat[1]) / 2;
                if (bit === 1) lat[0] = mid; else lat[1] = mid;
            }
            isEven = !isEven;
        }
    }
    return {
        latitude: Number(((lat[0] + lat[1]) / 2).toFixed(6)),
        longitude: Number(((lon[0] + lon[1]) / 2).toFixed(6)),
        latMin: lat[0], latMax: lat[1],
        lonMin: lon[0], lonMax: lon[1]
    };
}

function encodeGeohash(latitude, longitude, precision = 7) {
    if (!Number.isFinite(latitude) || !Number.isFinite(longitude) ||
        latitude < -90 || latitude > 90 || longitude < -180 || longitude > 180 ||
        !Number.isInteger(precision) || precision < 1 || precision > 12) {
        throw new RangeError('Coordinates or geohash precision are out of range.');
    }

    let isEven = true;
    let lat = [-90.0, 90.0];
    let lon = [-180.0, 180.0];
    let bit = 0;
    let ch = 0;
    let geohash = "";

    while (geohash.length < precision) {
        if (isEven) {
            let mid = (lon[0] + lon[1]) / 2;
            if (longitude >= mid) {
                ch |= (1 << (4 - bit));
                lon[0] = mid;
            } else {
                lon[1] = mid;
            }
        } else {
            let mid = (lat[0] + lat[1]) / 2;
            if (latitude >= mid) {
                ch |= (1 << (4 - bit));
                lat[0] = mid;
            } else {
                lat[1] = mid;
            }
        }
        isEven = !isEven;
        if (bit < 4) {
            bit++;
        } else {
            geohash += BASE32[ch];
            bit = 0;
            ch = 0;
        }
    }
    return geohash;
}

function isPointInRing(point, ring) {
    let x = point[0], y = point[1];
    let inside = false;
    for (let i = 0, j = ring.length - 1; i < ring.length; j = i++) {
        const xi = ring[i][0], yi = ring[i][1];
        const xj = ring[j][0], yj = ring[j][1];
        const intersect = ((yi > y) !== (yj > y)) && (x < (xj - xi) * (y - yi) / (yj - yi) + xi);
        if (intersect) inside = !inside;
    }
    return inside;
}

function isPointInPolygon(point, rings) {
    return rings.length > 0 && isPointInRing(point, rings[0]) &&
        !rings.slice(1).some(ring => isPointInRing(point, ring));
}

function collectGeoJSONGeometries(input) {
    if (!input || typeof input !== 'object') return [];
    if (input.type === 'FeatureCollection') {
        if (!Array.isArray(input.features)) throw new Error('GeoJSON FeatureCollection must include a features array.');
        return input.features.flatMap(collectGeoJSONGeometries);
    }
    if (input.type === 'Feature') {
        if (!input.geometry) return [];
        return collectGeoJSONGeometries(input.geometry);
    }
    if (input.type === 'GeometryCollection') {
        if (!Array.isArray(input.geometries)) throw new Error('GeoJSON GeometryCollection must include a geometries array.');
        return input.geometries.flatMap(collectGeoJSONGeometries);
    }
    if (['Point', 'MultiPoint', 'LineString', 'MultiLineString', 'Polygon', 'MultiPolygon'].includes(input.type)) {
        return [input];
    }
    throw new Error(`Unsupported GeoJSON type: ${input.type || 'unknown'}.`);
}

function getPointCoordinates(geometries) {
    const points = [];
    geometries.forEach(geometry => {
        if (geometry.type === 'Point') points.push(geometry.coordinates);
        else if (geometry.type === 'MultiPoint' || geometry.type === 'LineString') points.push(...geometry.coordinates);
        else if (geometry.type === 'MultiLineString') points.push(...geometry.coordinates.flat());
    });
    return points.filter(isValidCoordinate);
}

function isValidCoordinate(coordinate) {
    return Array.isArray(coordinate) && coordinate.length >= 2 &&
        coordinate[0] !== null && coordinate[1] !== null &&
        String(coordinate[0]).trim() !== '' && String(coordinate[1]).trim() !== '' &&
        Number.isFinite(Number(coordinate[0])) && Number.isFinite(Number(coordinate[1])) &&
        Number(coordinate[0]) >= -180 && Number(coordinate[0]) <= 180 &&
        Number(coordinate[1]) >= -90 && Number(coordinate[1]) <= 90;
}

function getPolygonCoordinates(geometry) {
    if (geometry.type === 'Polygon') return [geometry.coordinates];
    if (geometry.type === 'MultiPolygon') return geometry.coordinates;
    return [];
}

/* =========================================================================
   2. NAVIGATION & TAB SWITCHING LOGIC
   ========================================================================= */
let searchMap, genMap, polyMap, fenceMap, fenceImageMap;
let searchTileLayer, genTileLayer, polyTileLayer, fenceTileLayer, fenceImageOverlay;
let searchLayerGroup, genLayerGroup, polyLayerGroup, fenceMapLayers, fenceImageLayers, fenceLocatorLayer;
let searchResultsData = [];
let genResultsData = [];
let polyResultsData = [];
let searchEditMode = null;
let fenceFeatures = [];
let selectedFenceId = null;
let fenceDrawingType = null;
let fenceDrawingPoints = [];
let fencePreviewLayer = null;
let fenceFreehandActive = false;
let fenceVertexEditMode = false;
let fenceImageUrl = null;
let fenceImageDimensions = null;
let fenceActiveSurface = 'map';
let fenceFeatureCounter = 0;

const TILE_URLS = {
    dark: 'https://{s}.basemaps.cartocdn.com/dark_all/{z}/{x}/{y}{r}.png',
    satellite: 'https://server.arcgisonline.com/ArcGIS/rest/services/World_Imagery/MapServer/tile/{z}/{y}/{x}',
    light: 'https://{s}.basemaps.cartocdn.com/light_all/{z}/{x}/{y}{r}.png',
    street: 'https://tile.openstreetmap.org/{z}/{x}/{y}.png'
};

const CAMBODIA_PROVINCES = {
    'banteay-meanchey': { name: 'Banteay Meanchey', lat: 13.5859, lng: 102.9737 },
    battambang: { name: 'Battambang', lat: 13.0957, lng: 103.2022 },
    'kampong-cham': { name: 'Kampong Cham', lat: 11.9934, lng: 105.4635 },
    'kampong-chhnang': { name: 'Kampong Chhnang', lat: 12.25, lng: 104.6667 },
    'kampong-speu': { name: 'Kampong Speu', lat: 11.4533, lng: 104.5209 },
    'kampong-thom': { name: 'Kampong Thom', lat: 12.7111, lng: 104.8887 },
    kampot: { name: 'Kampot', lat: 10.6104, lng: 104.1815 },
    kandal: { name: 'Kandal', lat: 11.4833, lng: 104.95 },
    kep: { name: 'Kep', lat: 10.4829, lng: 104.3167 },
    'koh-kong': { name: 'Koh Kong', lat: 11.6153, lng: 102.9838 },
    kratie: { name: 'Kratie', lat: 12.4881, lng: 106.0188 },
    mondulkiri: { name: 'Mondulkiri', lat: 12.4558, lng: 107.1881 },
    'phnom-penh': { name: 'Phnom Penh', lat: 11.5564, lng: 104.9282 },
    'preah-vihear': { name: 'Preah Vihear', lat: 13.8073, lng: 104.9805 },
    'prey-veng': { name: 'Prey Veng', lat: 11.4868, lng: 105.3253 },
    pursat: { name: 'Pursat', lat: 12.5388, lng: 103.9192 },
    ratanakiri: { name: 'Ratanakiri', lat: 13.7394, lng: 106.9873 },
    'siem-reap': { name: 'Siem Reap', lat: 13.3671, lng: 103.8448 },
    'preah-sihanouk': { name: 'Preah Sihanouk', lat: 10.6259, lng: 103.5234 },
    'stung-treng': { name: 'Stung Treng', lat: 13.5259, lng: 105.9683 },
    'svay-rieng': { name: 'Svay Rieng', lat: 11.0879, lng: 105.7993 },
    takeo: { name: 'Takeo', lat: 10.9908, lng: 104.7849 },
    'oddar-meanchey': { name: 'Oddar Meanchey', lat: 14.1818, lng: 103.5176 },
    pailin: { name: 'Pailin', lat: 12.8489, lng: 102.6093 },
    'tboung-khmum': { name: 'Tboung Khmum', lat: 11.9117, lng: 105.6583 }
};

window.onload = function() {
    initSearchMap();
    initGenMap();
    initPolyMap();
    initFenceMaps();
    executeGeohashSearch();
};

function switchNavTab(tab) {
    ['home', 'search', 'generator', 'polygon', 'geofence', 'docs'].forEach(t => {
        const btn = document.getElementById(`nav-item-${t}`);
        const view = document.getElementById(`view-${t}`);
        if (t === tab) {
            btn.className = "w-full flex items-center space-x-3 px-3.5 py-2.5 rounded-xl transition text-white bg-grab shadow-lg shadow-grab/20 font-bold";
            view.classList.remove('hidden');
        } else {
            btn.className = "w-full flex items-center space-x-3 px-3.5 py-2.5 rounded-xl transition text-slate-400 hover:text-white hover:bg-slate-800/60 font-medium";
            view.classList.add('hidden');
        }
    });

    setTimeout(() => {
        if (tab === 'search' && searchMap) searchMap.invalidateSize();
        if (tab === 'generator' && genMap) genMap.invalidateSize();
        if (tab === 'polygon' && polyMap) polyMap.invalidateSize();
        if (tab === 'geofence' && fenceActiveSurface === 'map' && fenceMap) fenceMap.invalidateSize();
        if (tab === 'geofence' && fenceActiveSurface === 'image' && fenceImageMap) fenceImageMap.invalidateSize();
    }, 100);
}

/* =========================================================================
   3. MAP INITIALIZERS (CAMBODIA CENTERED [12.5657, 104.9910])
   ========================================================================= */
function initSearchMap() {
    searchMap = L.map('search-map', { zoomControl: false }).setView([12.5657, 104.9910], 8);
    searchTileLayer = createMapTileLayer(searchMap);
    L.control.zoom({ position: 'topright' }).addTo(searchMap);
    searchLayerGroup = L.layerGroup().addTo(searchMap);

    searchMap.on('click', function(e) {
        if (searchEditMode === 'add') {
            addSearchGeohashAt(e.latlng);
            return;
        }
        if (searchEditMode) return;
        document.getElementById('search-lat-input').value = e.latlng.lat.toFixed(6);
        document.getElementById('search-lng-input').value = e.latlng.lng.toFixed(6);
        const gh = encodeGeohash(e.latlng.lat, e.latlng.lng, 6);
        document.getElementById('search-geohash-input').value = gh;
        executeGeohashSearch();
    });
}

function initGenMap() {
    genMap = L.map('gen-map', { zoomControl: false }).setView([12.5657, 104.9910], 8);
    genTileLayer = createMapTileLayer(genMap);
    L.control.zoom({ position: 'topright' }).addTo(genMap);
    genLayerGroup = L.layerGroup().addTo(genMap);
}

function initPolyMap() {
    polyMap = L.map('poly-map', { zoomControl: false }).setView([12.5657, 104.9910], 8);
    polyTileLayer = createMapTileLayer(polyMap);
    L.control.zoom({ position: 'topright' }).addTo(polyMap);
    polyLayerGroup = L.layerGroup().addTo(polyMap);
}

function initFenceMaps() {
    fenceMap = L.map('fence-map', { zoomControl: false }).setView([12.5657, 104.9910], 8);
    fenceTileLayer = createMapTileLayer(fenceMap);
    L.control.zoom({ position: 'topright' }).addTo(fenceMap);
    fenceMapLayers = L.layerGroup().addTo(fenceMap);
    fenceLocatorLayer = L.layerGroup().addTo(fenceMap);
    fenceMap.on('click', event => handleFenceMapClick(event.latlng));
    bindFenceFreehandEvents(fenceMap);
    fenceMap.on('dblclick', event => {
        if (fenceDrawingType === 'polygon' || fenceDrawingType === 'polyline') {
            finishFenceDrawing();
            if (event.originalEvent) L.DomEvent.stop(event.originalEvent);
        }
    });

    fenceImageMap = L.map('fence-image-map', {
        crs: L.CRS.Simple,
        zoomControl: false,
        attributionControl: false,
        minZoom: -5,
        maxZoom: 3
    });
    fenceImageMap.createPane('fenceImagePane');
    fenceImageMap.getPane('fenceImagePane').style.zIndex = '200';
    fenceImageMap.getPane('fenceImagePane').style.pointerEvents = 'none';
    L.control.zoom({ position: 'topright' }).addTo(fenceImageMap);
    fenceImageLayers = L.layerGroup().addTo(fenceImageMap);
    fenceImageMap.on('click', event => handleFenceMapClick(event.latlng));
    bindFenceFreehandEvents(fenceImageMap);
    fenceImageMap.on('dblclick', event => {
        if (fenceDrawingType === 'polygon' || fenceDrawingType === 'polyline') {
            finishFenceDrawing();
            if (event.originalEvent) L.DomEvent.stop(event.originalEvent);
        }
    });
    renderFenceList();
}

function bindFenceFreehandEvents(map) {
    map.on('mousedown', event => {
        if (fenceActiveSurface !== (map === fenceMap ? 'map' : 'image') ||
            fenceDrawingType !== 'freehand-line') return;
        fenceFreehandActive = true;
        fenceDrawingPoints = [[event.latlng.lat, event.latlng.lng]];
        map.dragging.disable();
        renderFencePreview();
    });
    map.on('mousemove', event => {
        if (!fenceFreehandActive || activeFenceMap() !== map) return;
        const previous = fenceDrawingPoints[fenceDrawingPoints.length - 1];
        const distance = fenceActiveSurface === 'image'
            ? Math.hypot(event.latlng.lat - previous[0], event.latlng.lng - previous[1])
            : map.distance(L.latLng(previous[0], previous[1]), event.latlng);
        if (distance < 2) return;
        fenceDrawingPoints.push([event.latlng.lat, event.latlng.lng]);
        renderFencePreview();
    });
    map.on('mouseup', () => {
        if (!fenceFreehandActive || activeFenceMap() !== map) return;
        map.dragging.enable();
        fenceFreehandActive = false;
        if (fenceDrawingPoints.length < 2) {
            document.getElementById('fence-status').textContent = 'Drag farther to create a freehand line.';
            cancelFenceDrawing();
            return;
        }
        createFenceFeature('freehand-line', fenceDrawingPoints.slice(), null,
            document.getElementById('fence-poi-id').value.trim());
        cancelFenceDrawing();
    });
}

function createMapTileLayer(map) {
    return L.tileLayer(TILE_URLS.dark, {
        maxZoom: 19,
        attribution: '&copy; CartoDB, OpenStreetMap, Esri'
    }).addTo(map);
}

function changeMapTileLayer(type) {
    const tileUrl = TILE_URLS[type] || TILE_URLS.dark;
    [
        [searchMap, searchTileLayer],
        [genMap, genTileLayer],
        [polyMap, polyTileLayer],
        [fenceMap, fenceTileLayer]
    ].forEach(([map, currentLayer]) => {
        if (!map) return;
        if (currentLayer) map.removeLayer(currentLayer);
        const nextLayer = L.tileLayer(tileUrl, {
            maxZoom: 19,
            attribution: '&copy; CartoDB, OpenStreetMap, Esri'
        }).addTo(map);
        if (map === searchMap) searchTileLayer = nextLayer;
        if (map === genMap) genTileLayer = nextLayer;
        if (map === polyMap) polyTileLayer = nextLayer;
        if (map === fenceMap) fenceTileLayer = nextLayer;
    });
    document.querySelectorAll('.map-tile-switcher').forEach(select => {
        select.value = TILE_URLS[type] ? type : 'dark';
    });
}

function escapeHTML(value) {
    return String(value).replace(/[&<>"']/g, character => ({
        '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;'
    })[character]);
}

function activeFenceMap() {
    return fenceActiveSurface === 'map' ? fenceMap : fenceImageMap;
}

function activeFenceLayerGroup() {
    return fenceActiveSurface === 'map' ? fenceMapLayers : fenceImageLayers;
}

function setFenceSurface(surface) {
    if (surface === 'image' && !fenceImageDimensions) {
        document.getElementById('fence-status').textContent = 'Upload an image before switching to the image drawing surface.';
        return;
    }
    cancelFenceDrawing();
    fenceVertexEditMode = false;
    const editButton = document.getElementById('fence-edit-vertices-btn');
    editButton.setAttribute('aria-pressed', 'false');
    editButton.classList.remove('border-cyan-400');
    fenceActiveSurface = surface;
    document.getElementById('fence-map-stage').classList.toggle('hidden', surface !== 'map');
    document.getElementById('fence-image-stage').classList.toggle('hidden', surface !== 'image');
    document.getElementById('fence-map-mode-btn').setAttribute('aria-pressed', String(surface === 'map'));
    document.getElementById('fence-image-mode-btn').setAttribute('aria-pressed', String(surface === 'image'));
    document.getElementById('fence-map-mode-btn').className = surface === 'map'
        ? 'bg-cyan-600 text-white border border-cyan-500 font-bold py-2 rounded-lg text-[11px] transition'
        : 'bg-slate-800 text-slate-300 border border-slate-700 font-bold py-2 rounded-lg text-[11px] transition';
    document.getElementById('fence-image-mode-btn').className = surface === 'image'
        ? 'bg-cyan-600 text-white border border-cyan-500 font-bold py-2 rounded-lg text-[11px] transition'
        : 'bg-slate-800 text-slate-300 border border-slate-700 font-bold py-2 rounded-lg text-[11px] transition';
    renderFenceLayers();
    renderFenceList();
    window.setTimeout(() => activeFenceMap().invalidateSize(), 100);
}

function handleFenceImageUpload(event) {
    const file = event.target.files && event.target.files[0];
    if (!file) return;
    if (!file.type.startsWith('image/')) {
        document.getElementById('fence-status').textContent = 'Choose a supported image file.';
        event.target.value = '';
        return;
    }

    const nextUrl = URL.createObjectURL(file);
    const image = new Image();
    image.onerror = () => {
        URL.revokeObjectURL(nextUrl);
        document.getElementById('fence-status').textContent = 'Could not load the selected image.';
        event.target.value = '';
    };
    image.onload = () => {
        if (fenceImageUrl) URL.revokeObjectURL(fenceImageUrl);
        fenceImageUrl = nextUrl;
        fenceImageDimensions = { width: image.naturalWidth, height: image.naturalHeight, name: file.name };
        if (fenceImageOverlay) fenceImageMap.removeLayer(fenceImageOverlay);
        const bounds = [[0, 0], [image.naturalHeight, image.naturalWidth]];
        fenceImageOverlay = L.imageOverlay(fenceImageUrl, bounds, {
            pane: 'fenceImagePane',
            interactive: false
        }).addTo(fenceImageMap);
        document.getElementById('fence-image-placeholder').classList.add('hidden');
        document.getElementById('fence-image-name').textContent =
            `${file.name} · ${image.naturalWidth} × ${image.naturalHeight}px`;
        fenceImageMap.fitBounds(bounds);
        document.getElementById('fence-status').textContent =
            `Image ready. Image drawings use pixel coordinates and export separately from geographic GeoJSON.`;
        event.target.value = '';
        if (fenceActiveSurface === 'image') {
            window.setTimeout(() => fenceImageMap.invalidateSize(), 100);
        }
    };
    image.src = nextUrl;
}

function locateFencePOI() {
    const poiId = document.getElementById('fence-poi-id').value.trim();
    const latitudeText = document.getElementById('fence-lat').value.trim();
    const longitudeText = document.getElementById('fence-lng').value.trim();
    const latitude = Number(latitudeText);
    const longitude = Number(longitudeText);
    if (!latitudeText || !longitudeText || !isValidCoordinate([longitude, latitude])) {
        document.getElementById('fence-status').textContent =
            'Enter a valid latitude (−90 to 90) and longitude (−180 to 180).';
        return;
    }
    if (fenceActiveSurface !== 'map') setFenceSurface('map');
    fenceMap.setView([latitude, longitude], 17);
    fenceLocatorLayer.clearLayers();
    const label = poiId ? `POI ${escapeHTML(poiId)}` : 'Selected location';
    L.circleMarker([latitude, longitude], {
        radius: 8, color: '#fbbf24', weight: 3, fillColor: '#fbbf24',
        fillOpacity: 0.9, bubbleMouseEvents: false
    }).bindPopup(`<strong>${label}</strong><br>${latitude.toFixed(6)}, ${longitude.toFixed(6)}`)
        .addTo(fenceLocatorLayer);
    document.getElementById('fence-status').textContent =
        `${poiId ? `Located POI ${poiId}` : 'Located coordinates'} at ${latitude.toFixed(6)}, ${longitude.toFixed(6)}.`;
}

function addFencePOIPoint() {
    const poiId = document.getElementById('fence-poi-id').value.trim();
    const latitudeText = document.getElementById('fence-lat').value.trim();
    const longitudeText = document.getElementById('fence-lng').value.trim();
    const latitude = Number(latitudeText);
    const longitude = Number(longitudeText);
    if (!poiId) {
        document.getElementById('fence-status').textContent = 'Enter a POI ID to label the point fence.';
        return;
    }
    if (!latitudeText || !longitudeText || !isValidCoordinate([longitude, latitude])) {
        document.getElementById('fence-status').textContent = 'Enter valid latitude and longitude coordinates first.';
        return;
    }
    if (fenceActiveSurface !== 'map') setFenceSurface('map');
    createFenceFeature('marker', [[latitude, longitude]], null, poiId);
    fenceMap.setView([latitude, longitude], 17);
}

function startFenceDrawing(type) {
    if (![
        'marker', 'circle', 'rectangle', 'square', 'ellipse', 'triangle',
        'segment', 'horizontal-line', 'vertical-line', 'polyline', 'freehand-line', 'polygon', 'regular-polygon'
    ].includes(type)) return;
    if (fenceActiveSurface === 'image' && !fenceImageDimensions) {
        document.getElementById('fence-status').textContent = 'Upload an image before drawing on the image surface.';
        return;
    }
    cancelFenceDrawing();
    fenceVertexEditMode = false;
    selectedFenceId = null;
    document.getElementById('fence-apply-style-btn').disabled = true;
    document.getElementById('fence-edit-vertices-btn').disabled = true;
    document.getElementById('fence-edit-vertices-btn').setAttribute('aria-pressed', 'false');
    document.getElementById('fence-edit-vertices-btn').classList.remove('border-cyan-400');
    renderFenceLayers();
    fenceDrawingType = type;
    fenceDrawingPoints = [];
    activeFenceMap().doubleClickZoom.disable();
    activeFenceMap().getContainer().style.cursor = 'crosshair';
    const labels = {
        marker: 'Click once to place a point.',
        circle: 'Click the center to place a circle using the radius below.',
        rectangle: 'Click two opposite corners to create a rectangle.',
        square: 'Click two opposite corners. The tool keeps all sides equal.',
        ellipse: 'Click the center, then a point defining the horizontal and vertical radii.',
        triangle: 'Click three corners to create a triangle.',
        'regular-polygon': 'Click the center, then a point defining its radius. Set the number of sides below.',
        segment: 'Click two endpoints to create a straight line segment.',
        'horizontal-line': 'Click two points. The line stays level (constant latitude on a map).',
        'vertical-line': 'Click two points. The line stays upright (constant longitude on a map).',
        polyline: 'Click to add line vertices, then click Finish or double-click.',
        'freehand-line': 'Click and drag on the surface to draw a freehand line.',
        polygon: 'Click to add polygon vertices, then click Finish or double-click.'
    };
    document.getElementById('fence-draw-help').textContent = labels[type];
    document.getElementById('fence-finish-btn').disabled = !['polygon', 'polyline'].includes(type);
    document.getElementById('fence-undo-btn').disabled = true;
    document.getElementById('fence-status').textContent = `Drawing ${type}.`;
}

function handleFenceMapClick(latlng) {
    if (fenceDrawingType === 'freehand-line') return;
    if (!fenceDrawingType) {
        if (fenceActiveSurface === 'image' && fenceImageDimensions) {
            const x = Math.round(latlng.lng);
            const y = Math.round(fenceImageDimensions.height - latlng.lat);
            document.getElementById('fence-status').textContent = `Image position: x ${x}px, y ${y}px.`;
        }
        return;
    }

    if (fenceActiveSurface === 'map' && !isValidCoordinate([latlng.lng, latlng.lat])) {
        document.getElementById('fence-status').textContent = 'The clicked location is outside valid geographic coordinates.';
        return;
    }
    if (fenceActiveSurface === 'image' &&
        (latlng.lng < 0 || latlng.lng > fenceImageDimensions.width ||
         latlng.lat < 0 || latlng.lat > fenceImageDimensions.height)) {
        document.getElementById('fence-status').textContent = 'Draw inside the uploaded image bounds.';
        return;
    }

    if (fenceDrawingType === 'marker') {
        createFenceFeature('marker', [[latlng.lat, latlng.lng]], null, document.getElementById('fence-poi-id').value.trim());
        cancelFenceDrawing();
        return;
    }
    if (fenceDrawingType === 'circle') {
        const radius = Number(document.getElementById('fence-circle-radius').value);
        if (!Number.isFinite(radius) || radius <= 0) {
            document.getElementById('fence-status').textContent = 'Circle radius must be greater than zero.';
            return;
        }
        createFenceFeature('circle', [[latlng.lat, latlng.lng]], radius, document.getElementById('fence-poi-id').value.trim());
        cancelFenceDrawing();
        return;
    }
    if (fenceDrawingType === 'rectangle' && fenceDrawingPoints.length === 1) {
        const first = fenceDrawingPoints[0];
        createFenceFeature('rectangle', [first, [latlng.lat, latlng.lng]], null, document.getElementById('fence-poi-id').value.trim());
        cancelFenceDrawing();
        return;
    }

    const point = [latlng.lat, latlng.lng];
    if (fenceDrawingPoints.length && fenceDrawingType === 'horizontal-line') {
        point[0] = fenceDrawingPoints[0][0];
    } else if (fenceDrawingPoints.length && fenceDrawingType === 'vertical-line') {
        point[1] = fenceDrawingPoints[0][1];
    }
    fenceDrawingPoints.push(point);

    if (fenceDrawingPoints.length === 2 && fenceDrawingType === 'square') {
        createFenceFeature('square', createFenceSquarePoints(fenceDrawingPoints[0], fenceDrawingPoints[1]), null,
            document.getElementById('fence-poi-id').value.trim());
        cancelFenceDrawing();
        return;
    }
    if (fenceDrawingPoints.length === 2 && fenceDrawingType === 'ellipse') {
        try {
            createFenceFeature('ellipse', createFenceEllipsePoints(fenceDrawingPoints[0], fenceDrawingPoints[1]), null,
                document.getElementById('fence-poi-id').value.trim());
        } catch (error) {
            fenceDrawingPoints.pop();
            document.getElementById('fence-status').textContent = error.message;
            renderFencePreview();
            return;
        }
        cancelFenceDrawing();
        return;
    }
    if (fenceDrawingPoints.length === 2 && fenceDrawingType === 'regular-polygon') {
        const sides = Number(document.getElementById('fence-polygon-sides').value);
        if (!Number.isInteger(sides) || sides < 3 || sides > 12) {
            fenceDrawingPoints.pop();
            document.getElementById('fence-status').textContent = 'Regular polygons need between 3 and 12 sides.';
            renderFencePreview();
            return;
        }
        try {
            createFenceFeature('regular-polygon',
                createFenceEllipsePoints(fenceDrawingPoints[0], fenceDrawingPoints[1], sides), null,
                document.getElementById('fence-poi-id').value.trim());
        } catch (error) {
            fenceDrawingPoints.pop();
            document.getElementById('fence-status').textContent = error.message;
            renderFencePreview();
            return;
        }
        cancelFenceDrawing();
        return;
    }
    if (fenceDrawingPoints.length === 2 && ['segment', 'horizontal-line', 'vertical-line'].includes(fenceDrawingType)) {
        createFenceFeature(fenceDrawingType, fenceDrawingPoints.slice(), null,
            document.getElementById('fence-poi-id').value.trim());
        cancelFenceDrawing();
        return;
    }
    if (fenceDrawingPoints.length === 3 && fenceDrawingType === 'triangle') {
        createFenceFeature('triangle', fenceDrawingPoints.slice(), null,
            document.getElementById('fence-poi-id').value.trim());
        cancelFenceDrawing();
        return;
    }

    document.getElementById('fence-finish-btn').disabled =
        (fenceDrawingType === 'polygon' && fenceDrawingPoints.length < 3) ||
        (fenceDrawingType === 'polyline' && fenceDrawingPoints.length < 2);
    document.getElementById('fence-undo-btn').disabled = false;
    renderFencePreview();
    document.getElementById('fence-status').textContent = `${fenceDrawingPoints.length} point${fenceDrawingPoints.length === 1 ? '' : 's'} added.`;
}

function createFenceSquarePoints(first, opposite) {
    if (fenceActiveSurface === 'image') {
        const side = Math.max(Math.abs(opposite[0] - first[0]), Math.abs(opposite[1] - first[1]));
        const latDirection = opposite[0] >= first[0] ? 1 : -1;
        const lngDirection = opposite[1] >= first[1] ? 1 : -1;
        return [
            first.slice(),
            [first[0] + side * latDirection, first[1]],
            [first[0] + side * latDirection, first[1] + side * lngDirection],
            [first[0], first[1] + side * lngDirection]
        ];
    }
    const map = activeFenceMap();
    const zoom = map.getZoom();
    const start = map.project(L.latLng(first[0], first[1]), zoom);
    const end = map.project(L.latLng(opposite[0], opposite[1]), zoom);
    const side = Math.max(Math.abs(end.x - start.x), Math.abs(end.y - start.y));
    const xDirection = end.x >= start.x ? 1 : -1;
    const yDirection = end.y >= start.y ? 1 : -1;
    return [
        map.unproject(start, zoom),
        map.unproject(L.point(start.x, start.y + side * yDirection), zoom),
        map.unproject(L.point(start.x + side * xDirection, start.y + side * yDirection), zoom),
        map.unproject(L.point(start.x + side * xDirection, start.y), zoom)
    ].map(point => [point.lat, point.lng]);
}

function createFenceEllipsePoints(center, edge, sides = 64) {
    const radiusLat = Math.abs(edge[0] - center[0]);
    const radiusLng = Math.abs(edge[1] - center[1]);
    if (!radiusLat && !radiusLng) throw new Error('Ellipse must have a non-zero width and height.');
    return Array.from({ length: sides }, (_, index) => {
        const angle = (index / sides) * Math.PI * 2;
        return [
            center[0] + Math.sin(angle) * radiusLat,
            center[1] + Math.cos(angle) * radiusLng
        ];
    });
}

function getFenceStyleFromInputs() {
    const width = Number(document.getElementById('fence-stroke-width').value);
    if (!Number.isInteger(width) || width < 1 || width > 10) {
        throw new Error('Line width must be a whole number between 1 and 10.');
    }
    return {
        color: document.getElementById('fence-stroke-color').value,
        fillColor: document.getElementById('fence-fill-color').value,
        fillOpacity: Number(document.getElementById('fence-opacity').value) / 100,
        weight: width,
        dashArray: {
            solid: null,
            dashed: '8 6',
            dotted: '2 6'
        }[document.getElementById('fence-line-pattern').value]
    };
}

function createFenceFeature(type, points, radius, poiId = '') {
    if (fenceActiveSurface === 'map' && points.some(([latitude, longitude]) => !isValidCoordinate([longitude, latitude]))) {
        document.getElementById('fence-status').textContent = 'The shape extends outside valid geographic coordinates.';
        return;
    }
    if (fenceActiveSurface === 'image' && points.some(([y, x]) =>
        x < 0 || x > fenceImageDimensions.width || y < 0 || y > fenceImageDimensions.height)) {
        document.getElementById('fence-status').textContent = 'The shape extends outside the uploaded image bounds.';
        return;
    }
    let style;
    try {
        style = getFenceStyleFromInputs();
    } catch (error) {
        document.getElementById('fence-status').textContent = error.message;
        return;
    }
    fenceFeatureCounter++;
    const feature = {
        id: `fence-${fenceFeatureCounter}`,
        type,
        surface: fenceActiveSurface,
        points,
        radius,
        poiId,
        style
    };
    fenceFeatures.push(feature);
    selectedFenceId = feature.id;
    document.getElementById('fence-apply-style-btn').disabled = false;
    document.getElementById('fence-edit-vertices-btn').disabled = false;
    renderFenceLayers();
    renderFenceList();
    document.getElementById('fence-status').textContent = `${type[0].toUpperCase()}${type.slice(1)} fence added.`;
}

function renderFenceLayers() {
    if (!fenceMapLayers || !fenceImageLayers) return;
    fenceMapLayers.clearLayers();
    fenceImageLayers.clearLayers();
    fenceFeatures.filter(feature => feature.surface === 'map' || feature.surface === 'image').forEach(feature => {
        const group = feature.surface === 'map' ? fenceMapLayers : fenceImageLayers;
        const style = { ...feature.style, bubbleMouseEvents: false };
        let layer;
        if (feature.type === 'marker') {
            layer = L.circleMarker(feature.points[0], {
                ...style, radius: 7, fillColor: feature.style.fillColor, fillOpacity: Math.max(feature.style.fillOpacity, 0.65)
            });
        } else if (feature.type === 'circle') {
            layer = L.circle(feature.points[0], { ...style, radius: feature.radius });
        } else if (feature.type === 'rectangle') {
            layer = L.rectangle(feature.points, style);
        } else if (['polygon', 'square', 'ellipse', 'triangle', 'regular-polygon'].includes(feature.type)) {
            layer = L.polygon(feature.points, style);
        } else {
            layer = L.polyline(feature.points, style);
        }
        const selected = feature.id === selectedFenceId;
        if (selected) layer.setStyle({ weight: Math.min(feature.style.weight + 2, 12) });
        const description = feature.poiId ? `<br>POI: ${escapeHTML(feature.poiId)}` : '';
        layer.bindPopup(`<strong>${escapeHTML(feature.type)}</strong>${description}`);
        layer.on('click', () => selectFenceFeature(feature.id));
        layer.addTo(group);
        if (feature.id === selectedFenceId && fenceVertexEditMode) {
            feature.points.forEach((point, index) => {
                const handle = L.marker(point, {
                    draggable: true,
                    icon: L.divIcon({ className: 'fence-vertex-handle', iconSize: [12, 12], iconAnchor: [6, 6] }),
                    zIndexOffset: 1000
                });
                handle.on('dragend', event => {
                    const position = event.target.getLatLng();
                    if (feature.surface === 'map' && !isValidCoordinate([position.lng, position.lat])) {
                        document.getElementById('fence-status').textContent = 'A vertex must remain within valid geographic coordinates.';
                        renderFenceLayers();
                        return;
                    }
                    if (feature.surface === 'image' &&
                        (position.lng < 0 || position.lng > fenceImageDimensions.width ||
                         position.lat < 0 || position.lat > fenceImageDimensions.height)) {
                        document.getElementById('fence-status').textContent = 'Keep image fence vertices within the image bounds.';
                        renderFenceLayers();
                        return;
                    }
                    const point = [position.lat, position.lng];
                    if (feature.type === 'vertical-line' && feature.points.length > 1) {
                        point[1] = feature.points[0][1];
                    } else if (feature.type === 'horizontal-line' && feature.points.length > 1) {
                        point[0] = feature.points[0][0];
                    }
                    feature.points[index] = point;
                    document.getElementById('fence-status').textContent = 'Fence vertex updated.';
                    renderFenceLayers();
                    renderFenceList();
                });
                handle.addTo(group);
            });
        }
    });
    renderFencePreview();
}

function renderFencePreview() {
    const group = activeFenceLayerGroup();
    if (fencePreviewLayer && group.hasLayer(fencePreviewLayer)) group.removeLayer(fencePreviewLayer);
    fencePreviewLayer = null;
    if (!fenceDrawingType || !fenceDrawingPoints.length) return;
    const style = { color: '#fbbf24', weight: 2, dashArray: '5 5', fillOpacity: 0.1, bubbleMouseEvents: false };
    if (fenceDrawingType === 'rectangle' && fenceDrawingPoints.length === 2) {
        fencePreviewLayer = L.rectangle(fenceDrawingPoints, style);
    } else if (fenceDrawingType === 'square' && fenceDrawingPoints.length === 2) {
        fencePreviewLayer = L.polygon(createFenceSquarePoints(fenceDrawingPoints[0], fenceDrawingPoints[1]), style);
    } else if (fenceDrawingType === 'ellipse' && fenceDrawingPoints.length === 2) {
        fencePreviewLayer = L.polygon(createFenceEllipsePoints(fenceDrawingPoints[0], fenceDrawingPoints[1]), style);
    } else if (fenceDrawingType === 'regular-polygon' && fenceDrawingPoints.length === 2) {
        const sides = Number(document.getElementById('fence-polygon-sides').value);
        if (Number.isInteger(sides) && sides >= 3 && sides <= 12) {
            fencePreviewLayer = L.polygon(createFenceEllipsePoints(fenceDrawingPoints[0], fenceDrawingPoints[1], sides), style);
        }
    } else if (fenceDrawingType === 'circle') {
        fencePreviewLayer = L.circle(fenceDrawingPoints[0], {
            ...style, radius: Number(document.getElementById('fence-circle-radius').value) || 1
        });
    } else if (fenceDrawingType === 'polygon' && fenceDrawingPoints.length >= 3) {
        fencePreviewLayer = L.polygon(fenceDrawingPoints, style);
    } else if (fenceDrawingPoints.length >= 2) {
        fencePreviewLayer = L.polyline(fenceDrawingPoints, style);
    } else {
        fencePreviewLayer = L.circleMarker(fenceDrawingPoints[0], { ...style, radius: 5 });
    }
    fencePreviewLayer.addTo(group);
}

function finishFenceDrawing() {
    if (!fenceDrawingType) return;
    const type = fenceDrawingType;
    const points = fenceDrawingPoints.filter((point, index, list) =>
        index === 0 || Math.abs(point[0] - list[index - 1][0]) > 1e-10 ||
        Math.abs(point[1] - list[index - 1][1]) > 1e-10
    );
    if (type === 'polygon' && points.length > 1 &&
        Math.abs(points[0][0] - points[points.length - 1][0]) <= 1e-10 &&
        Math.abs(points[0][1] - points[points.length - 1][1]) <= 1e-10) {
        points.pop();
    }
    const minimum = type === 'polygon' ? 3 : 2;
    if (!['polygon', 'polyline'].includes(type) || points.length < minimum) {
        document.getElementById('fence-status').textContent = `${type} needs at least ${minimum} points.`;
        return;
    }
    createFenceFeature(type, points, null, document.getElementById('fence-poi-id').value.trim());
    cancelFenceDrawing();
}

function undoFenceVertex() {
    if (!fenceDrawingPoints.length) return;
    fenceDrawingPoints.pop();
    document.getElementById('fence-finish-btn').disabled =
        (fenceDrawingType === 'polygon' && fenceDrawingPoints.length < 3) ||
        (fenceDrawingType === 'polyline' && fenceDrawingPoints.length < 2);
    document.getElementById('fence-undo-btn').disabled = fenceDrawingPoints.length === 0;
    renderFencePreview();
}

function cancelFenceDrawing() {
    fenceFreehandActive = false;
    if (fencePreviewLayer && activeFenceLayerGroup() && activeFenceLayerGroup().hasLayer(fencePreviewLayer)) {
        activeFenceLayerGroup().removeLayer(fencePreviewLayer);
    }
    fencePreviewLayer = null;
    fenceDrawingType = null;
    fenceDrawingPoints = [];
    if (fenceMap) {
        fenceMap.doubleClickZoom.enable();
        fenceMap.dragging.enable();
        fenceMap.getContainer().style.cursor = '';
    }
    if (fenceImageMap) {
        fenceImageMap.doubleClickZoom.enable();
        fenceImageMap.dragging.enable();
        fenceImageMap.getContainer().style.cursor = '';
    }
    const finish = document.getElementById('fence-finish-btn');
    const undo = document.getElementById('fence-undo-btn');
    if (finish) finish.disabled = true;
    if (undo) undo.disabled = true;
    const help = document.getElementById('fence-draw-help');
    if (help) help.textContent = 'Choose a shape, then click on the active surface. Finish lines and polygons with the button below.';
}

function selectFenceFeature(id) {
    selectedFenceId = id;
    const feature = fenceFeatures.find(item => item.id === id);
    if (feature) {
        document.getElementById('fence-stroke-color').value = feature.style.color;
        document.getElementById('fence-fill-color').value = feature.style.fillColor;
        document.getElementById('fence-opacity').value = Math.round(feature.style.fillOpacity * 100);
        document.getElementById('fence-opacity-value').textContent = `${Math.round(feature.style.fillOpacity * 100)}%`;
        document.getElementById('fence-stroke-width').value = feature.style.weight;
        document.getElementById('fence-line-pattern').value =
            feature.style.dashArray === '8 6' ? 'dashed' :
                feature.style.dashArray === '2 6' ? 'dotted' : 'solid';
        document.getElementById('fence-apply-style-btn').disabled = false;
        document.getElementById('fence-circle-radius').value = feature.type === 'circle'
            ? feature.radius
            : document.getElementById('fence-circle-radius').value;
        document.getElementById('fence-edit-vertices-btn').disabled = false;
        if (feature.surface !== fenceActiveSurface) setFenceSurface(feature.surface);
    }
    renderFenceLayers();
    renderFenceList();
}

function applyFenceStyle() {
    const feature = fenceFeatures.find(item => item.id === selectedFenceId);
    if (!feature) return;
    try {
        const style = getFenceStyleFromInputs();
        let radius;
        if (feature.type === 'circle') {
            radius = Number(document.getElementById('fence-circle-radius').value);
            if (!Number.isFinite(radius) || radius <= 0) throw new Error('Circle radius must be greater than zero.');
        }
        feature.style = style;
        if (feature.type === 'circle') feature.radius = radius;
        renderFenceLayers();
        renderFenceList();
        document.getElementById('fence-status').textContent = 'Style applied to the selected fence.';
    } catch (error) {
        document.getElementById('fence-status').textContent = error.message;
    }
}

function toggleFenceVertexEdit() {
    if (!selectedFenceId) return;
    fenceVertexEditMode = !fenceVertexEditMode;
    document.getElementById('fence-edit-vertices-btn').setAttribute('aria-pressed', String(fenceVertexEditMode));
    document.getElementById('fence-edit-vertices-btn').classList.toggle('border-cyan-400', fenceVertexEditMode);
    renderFenceLayers();
    document.getElementById('fence-status').textContent = fenceVertexEditMode
        ? 'Drag the yellow handles to adjust the selected shape.'
        : 'Vertex editing disabled.';
}

function deleteFenceFeature(id) {
    fenceFeatures = fenceFeatures.filter(feature => feature.id !== id);
    if (selectedFenceId === id) {
        selectedFenceId = null;
        fenceVertexEditMode = false;
        document.getElementById('fence-apply-style-btn').disabled = true;
        document.getElementById('fence-edit-vertices-btn').disabled = true;
        document.getElementById('fence-edit-vertices-btn').setAttribute('aria-pressed', 'false');
        document.getElementById('fence-edit-vertices-btn').classList.remove('border-cyan-400');
    }
    renderFenceLayers();
    renderFenceList();
    document.getElementById('fence-status').textContent = 'Fence removed.';
}

function renderFenceList() {
    const container = document.getElementById('fence-list');
    if (!container) return;
    const visibleFeatures = fenceFeatures.filter(feature => feature.surface === fenceActiveSurface);
    document.getElementById('fence-count').textContent = `${visibleFeatures.length} on ${fenceActiveSurface}`;
    container.innerHTML = visibleFeatures.map((feature, index) => `
        <div class="flex items-center gap-1">
            <button type="button" onclick="selectFenceFeature('${feature.id}')" class="flex-1 min-w-0 text-left p-2 rounded-lg border ${feature.id === selectedFenceId ? 'border-amber-400 bg-slate-900' : 'border-slate-800 bg-slate-900/60'}">
                <span class="block truncate text-white font-semibold">${escapeHTML(feature.poiId || `${feature.type[0].toUpperCase()}${feature.type.slice(1)} ${index + 1}`)}</span>
                <span class="block text-[10px] text-slate-400">${escapeHTML(feature.type)}${feature.type === 'circle' ? ` · r ${feature.radius}` : ''}</span>
            </button>
            <button type="button" aria-label="Delete fence ${index + 1}" onclick="deleteFenceFeature('${feature.id}')" class="p-2 text-rose-300 hover:bg-rose-950 rounded-lg"><i class="fa-solid fa-trash"></i></button>
        </div>
    `).join('') || '<p class="text-[10px] text-slate-500">No fences on this surface yet.</p>';
}

function clearFences() {
    if (!fenceFeatures.length) {
        cancelFenceDrawing();
        return;
    }
    if (!window.confirm('Delete all drawn geofences on both the map and image?')) return;
    cancelFenceDrawing();
    fenceFeatures = [];
    selectedFenceId = null;
    fenceVertexEditMode = false;
    fenceLocatorLayer.clearLayers();
    document.getElementById('fence-apply-style-btn').disabled = true;
    document.getElementById('fence-edit-vertices-btn').disabled = true;
    document.getElementById('fence-edit-vertices-btn').setAttribute('aria-pressed', 'false');
    document.getElementById('fence-edit-vertices-btn').classList.remove('border-cyan-400');
    renderFenceLayers();
    renderFenceList();
    document.getElementById('fence-status').textContent = 'All geofences cleared.';
}

function exportFences() {
    const visibleFeatures = fenceFeatures.filter(feature => feature.surface === fenceActiveSurface);
    if (!visibleFeatures.length) {
        document.getElementById('fence-status').textContent = 'There are no geofences on this surface to export.';
        return;
    }
    if (fenceActiveSurface === 'image') {
        const imageExport = {
            type: 'ImageGeofenceCollection',
            image: fenceImageDimensions,
            coordinateSystem: 'image-pixels-origin-top-left',
            features: visibleFeatures.map(feature => ({
                id: feature.id,
                type: feature.type,
                poiId: feature.poiId || null,
                style: feature.style,
                radius: feature.radius,
                coordinates: feature.points.map(([latitude, longitude]) => ({
                    x: Number(longitude.toFixed(2)),
                    y: Number((fenceImageDimensions.height - latitude).toFixed(2))
                }))
            }))
        };
        downloadFile(JSON.stringify(imageExport, null, 2), 'image_geofences.json', 'application/json');
        document.getElementById('fence-status').textContent = 'Image geofences exported with image-pixel coordinates.';
        return;
    }

    const features = visibleFeatures.map(feature => {
        let geometry;
        if (feature.type === 'marker') {
            const [latitude, longitude] = feature.points[0];
            geometry = { type: 'Point', coordinates: [longitude, latitude] };
        } else if (feature.type === 'circle') {
            const [latitude, longitude] = feature.points[0];
            const ring = [];
            for (let index = 0; index <= 64; index++) {
                const angle = (index / 64) * Math.PI * 2;
                const angularDistance = feature.radius / 6371008.8;
                const lat1 = latitude * Math.PI / 180;
                const lon1 = longitude * Math.PI / 180;
                const lat2 = Math.asin(Math.sin(lat1) * Math.cos(angularDistance) +
                    Math.cos(lat1) * Math.sin(angularDistance) * Math.cos(angle));
                const lon2 = lon1 + Math.atan2(
                    Math.sin(angle) * Math.sin(angularDistance) * Math.cos(lat1),
                    Math.cos(angularDistance) - Math.sin(lat1) * Math.sin(lat2)
                );
                const wrappedLongitude = ((lon2 * 180 / Math.PI + 540) % 360) - 180;
                ring.push([wrappedLongitude, lat2 * 180 / Math.PI]);
            }
            geometry = { type: 'Polygon', coordinates: [ring] };
        } else {
            const points = feature.type === 'rectangle'
                ? [[Math.min(feature.points[0][0], feature.points[1][0]), Math.min(feature.points[0][1], feature.points[1][1])],
                    [Math.min(feature.points[0][0], feature.points[1][0]), Math.max(feature.points[0][1], feature.points[1][1])],
                    [Math.max(feature.points[0][0], feature.points[1][0]), Math.max(feature.points[0][1], feature.points[1][1])],
                    [Math.max(feature.points[0][0], feature.points[1][0]), Math.min(feature.points[0][1], feature.points[1][1])]]
                : feature.points;
            const coordinates = points.map(([latitude, longitude]) => [longitude, latitude]);
            if ([
                'rectangle', 'polygon', 'square', 'ellipse', 'triangle', 'regular-polygon'
            ].includes(feature.type)) {
                coordinates.push(coordinates[0].slice());
                geometry = { type: 'Polygon', coordinates: [coordinates] };
            } else {
                geometry = { type: 'LineString', coordinates };
            }
        }
        return {
            type: 'Feature',
            properties: { id: feature.id, shape: feature.type, poi_id: feature.poiId || null, radius_meters: feature.type === 'circle' ? feature.radius : null, style: feature.style },
            geometry
        };
    });
    downloadFile(JSON.stringify({ type: 'FeatureCollection', features }, null, 2), 'geofences.geojson', 'application/geo+json');
    document.getElementById('fence-status').textContent = 'Geographic fences exported as GeoJSON.';
}

/* =========================================================================
   4. GEOHASH SEARCH HANDLERS
   ========================================================================= */
function executeGeohashSearch() {
    setSearchEditMode(null);
    const geohashInput = document.getElementById('search-geohash-input').value.trim();
    const latRaw = document.getElementById('search-lat-input').value.trim();
    const lngRaw = document.getElementById('search-lng-input').value.trim();
    const hasCoordinateInput = Boolean(latRaw || lngRaw);
    const latInput = Number(latRaw);
    const lngInput = Number(lngRaw);
    const precision = 6;
    searchResultsData = [];
    let invalidCount = 0;
    const coordinates = [];

    if (hasCoordinateInput) {
        if (latRaw && lngRaw && isValidCoordinate([lngInput, latInput])) {
            coordinates.push([lngInput, latInput]);
        } else {
            invalidCount++;
        }
    } else if (geohashInput) {
        geohashInput.split(/\r?\n/).forEach(line => {
            const coordinateMatch = line.match(/^\s*[\[(]?\s*(-?\d+(?:\.\d+)?)\s*[,;\s]\s*(-?\d+(?:\.\d+)?)\s*[\])]?\s*$/);
            if (coordinateMatch) {
                const lngLat = [Number(coordinateMatch[2]), Number(coordinateMatch[1])];
                if (isValidCoordinate(lngLat)) coordinates.push(lngLat);
                else invalidCount++;
                return;
            }

            const values = line.replace(/(?:geohash|hash|gh)\s*[:=]\s*/ig, '')
                .split(/[\s,;|]+/)
                .map(value => value.replace(/^[\[\]{}"'`]+|[\[\]{}"'`]+$/g, '').trim())
                .filter(Boolean);
            values.forEach(value => {
                const code = value.toLowerCase();
                const decoded = decodeGeohash(code);
                if (decoded) searchResultsData.push({ code, ...decoded });
                else invalidCount++;
            });
        });
    }

    if (searchResultsData.length > MAX_RESULT_ITEMS) {
        searchResultsData = [];
        document.getElementById('search-status').textContent =
            `Search is limited to ${MAX_RESULT_ITEMS.toLocaleString()} geohashes at a time.`;
        renderSearchGeohashes(true);
        return;
    }

    coordinates.forEach(coordinate => {
        const code = encodeGeohash(coordinate[1], coordinate[0], precision);
        const decoded = decodeGeohash(code);
        if (decoded && !searchResultsData.some(item => item.code === code)) {
            searchResultsData.push({ code, ...decoded });
        }
    });

    const status = document.getElementById('search-status');
    if (searchResultsData.length > MAX_RESULT_ITEMS) {
        searchResultsData = [];
        status.textContent = `Search is limited to ${MAX_RESULT_ITEMS.toLocaleString()} geohashes at a time.`;
        renderSearchGeohashes(true);
        return;
    }
    status.textContent = searchResultsData.length
        ? `${searchResultsData.length} geohash cell${searchResultsData.length === 1 ? '' : 's'} found${invalidCount ? `; ${invalidCount} invalid entr${invalidCount === 1 ? 'y' : 'ies'} skipped` : ''}.`
        : 'No valid geohashes or coordinates found. Enter geohash strings, coordinate pairs, or upload GeoJSON.';
    renderSearchGeohashes(true);
}

function handleSearchGeoJSONUpload(event) {
    const file = event.target.files && event.target.files[0];
    if (!file) return;
    const status = document.getElementById('search-status');
    const reader = new FileReader();
    reader.onerror = () => { status.textContent = 'Could not read the selected GeoJSON file.'; };
    reader.onload = () => {
        try {
            const geometries = collectGeoJSONGeometries(JSON.parse(String(reader.result)));
            const precision = Number(document.getElementById('search-geojson-precision').value);
            const codes = new Set();
            getPointCoordinates(geometries).forEach(([longitude, latitude]) => {
                codes.add(encodeGeohash(latitude, longitude, precision));
            });
            geometries.forEach(geometry => {
                getPolygonCoordinates(geometry).forEach(polygon => {
                    getPolygonGeohashCover(polygon, precision).forEach(item => codes.add(item.code));
                });
            });
            if (!codes.size) throw new Error('The GeoJSON contains no supported points or polygon boundaries.');
            if (codes.size > MAX_RESULT_ITEMS) {
                throw new Error(`The GeoJSON produces more than ${MAX_RESULT_ITEMS.toLocaleString()} cells. Choose a lower precision or a smaller area.`);
            }
            searchResultsData = Array.from(codes, code => ({ code, ...decodeGeohash(code) }));
            document.getElementById('search-geohash-input').value = '';
            document.getElementById('search-lat-input').value = '';
            document.getElementById('search-lng-input').value = '';
            status.textContent = `Loaded ${file.name}: ${searchResultsData.length} geohash cells at precision ${precision}.`;
            setSearchEditMode(null);
            renderSearchGeohashes(true);
        } catch (error) {
            status.textContent = `GeoJSON search failed: ${error.message}`;
        } finally {
            event.target.value = '';
        }
    };
    reader.readAsText(file);
}

function renderSearchGeohashes(fitToResults) {
    searchLayerGroup.clearLayers();
    const boundsArray = [];

    searchResultsData.forEach(item => {
        const bounds = [[item.latMin, item.lonMin], [item.latMax, item.lonMax]];
        boundsArray.push(bounds);
        const rect = L.rectangle(bounds, {
            color: '#00b14f',
            weight: 2,
            fillColor: '#00b14f',
            fillOpacity: 0.25
        });
        rect.bindPopup(`
            <div class="p-1 font-mono text-xs">
                <span class="text-grab font-bold uppercase">${item.code}</span>
                <p class="text-slate-300 mt-1">Lat: ${item.latitude}</p>
                <p class="text-slate-300">Lng: ${item.longitude}</p>
            </div>
        `);
        rect.on('click', function(e) {
            handleSearchGeohashClick(item.code, e.latlng);
        });
        searchLayerGroup.addLayer(rect);
    });

    if (fitToResults && boundsArray.length > 0) {
        searchMap.fitBounds(L.latLngBounds(boundsArray.flat()), { padding: [50, 50] });
    }
    document.getElementById('search-count-badge').innerText = `${searchResultsData.length} Geohashes`;
    const container = document.getElementById('search-details-container');
    container.innerHTML = searchResultsData.map(item => `
        <div class="p-2 bg-slate-900 rounded-lg border border-slate-800">
            <div class="text-grab font-bold">${item.code}</div>
            <div class="text-[10px] text-slate-400">Centroid: ${item.latitude}, ${item.longitude}</div>
        </div>
    `).join('');
}

function setSearchEditMode(mode) {
    searchEditMode = mode;

    const addButton = document.getElementById('search-add-grid-btn');
    const deleteButton = document.getElementById('search-delete-grid-btn');
    const finishButton = document.getElementById('search-finish-edit-btn');
    const status = document.getElementById('search-edit-status');
    [addButton, deleteButton].forEach(button => {
        button.classList.remove('bg-grab', 'border-grab', 'text-white');
        button.classList.add('bg-slate-800', 'border-slate-700');
        button.setAttribute('aria-pressed', 'false');
    });

    if (mode === 'add') {
        addButton.classList.add('bg-grab', 'border-grab', 'text-white');
        addButton.setAttribute('aria-pressed', 'true');
        status.textContent = 'Click the map to add one cell at the selected precision. Click more places to add more cells.';
    } else if (mode === 'delete') {
        deleteButton.classList.add('bg-grab', 'border-grab', 'text-white');
        deleteButton.setAttribute('aria-pressed', 'true');
        status.textContent = 'Click a cell on the map to delete it.';
    } else {
        status.textContent = 'Choose an edit action to change the displayed grid.';
    }

    finishButton.classList.toggle('hidden', !mode);
    if (searchMap) {
        if (mode) searchMap.doubleClickZoom.disable();
        else searchMap.doubleClickZoom.enable();
    }
}

function handleSearchGeohashClick(code, latlng) {
    if (searchEditMode === 'add') {
        addSearchGeohashAt(latlng);
    } else if (searchEditMode === 'delete') {
        deleteSearchGeohash(code);
    }
}

function addSearchGeohashAt(latlng) {
    const precision = Number(document.getElementById('search-add-precision').value);
    const code = encodeGeohash(latlng.lat, latlng.lng, precision);
    if (searchResultsData.some(item => item.code === code)) {
        document.getElementById('search-edit-status').textContent =
            `${code} is already in the grid. Click a different area to add another cell.`;
        return;
    }

    const decoded = decodeGeohash(code);
    if (!decoded) {
        document.getElementById('search-edit-status').textContent =
            `Could not create a geohash for this location.`;
        return;
    }

    searchResultsData.push({ code, ...decoded });
    document.getElementById('search-geohash-input').value =
        searchResultsData.map(item => item.code).join(', ');
    document.getElementById('search-edit-status').textContent = `Added ${code}. Click the map to add another cell.`;
    renderSearchGeohashes(false);
}

function deleteSearchGeohash(code) {
    searchResultsData = searchResultsData.filter(item => item.code !== code);
    document.getElementById('search-geohash-input').value =
        searchResultsData.map(item => item.code).join(', ');
    document.getElementById('search-edit-status').textContent = `Deleted ${code}.`;
    renderSearchGeohashes(false);
}

function applySearchPreset(code, lat, lng) {
    document.getElementById('search-geohash-input').value = code;
    document.getElementById('search-lat-input').value = lat;
    document.getElementById('search-lng-input').value = lng;
    executeGeohashSearch();
}

function applyCambodiaProvince(provinceId) {
    const province = CAMBODIA_PROVINCES[provinceId];
    if (!province) return;

    const code = encodeGeohash(province.lat, province.lng, 6);
    document.getElementById('search-geohash-input').value = code;
    document.getElementById('search-lat-input').value = province.lat;
    document.getElementById('search-lng-input').value = province.lng;
    executeGeohashSearch();
}

/* =========================================================================
   5. GEOHASH GENERATOR HANDLERS
   ========================================================================= */
function updatePrecisionSlider(val) {
    document.getElementById('slider-precision-val').innerText = `${val} Characters`;
}

function generateBatchGeohashes() {
    const rawText = document.getElementById('gen-coords-input').value.trim();
    const precision = Number(document.getElementById('precision-slider').value);
    const status = document.getElementById('gen-status');
    genLayerGroup.clearLayers();
    genResultsData = [];

    if (!rawText) {
        status.textContent = 'Add coordinate pairs or upload a file before generating.';
        renderGeneratorResults();
        return;
    }

    let rows = rawText.split(/\r?\n/).map(line => line.trim()).filter(Boolean);
    if (rows.length > MAX_RESULT_ITEMS) {
        status.textContent = `Generation is limited to ${MAX_RESULT_ITEMS.toLocaleString()} coordinate rows at a time.`;
        renderGeneratorResults();
        return;
    }
    let latitudeIndex = 0, longitudeIndex = 1;
    const firstColumns = splitCSVRow(rows[0]).map(value => value.toLowerCase().replace(/[*_\s-]/g, ''));
    const headerLatIndex = firstColumns.findIndex(value => ['lat', 'latitude', 'y'].includes(value));
    const headerLngIndex = firstColumns.findIndex(value => ['lon', 'lng', 'longitude', 'x'].includes(value));
    if (headerLatIndex !== -1 && headerLngIndex !== -1) {
        latitudeIndex = headerLatIndex;
        longitudeIndex = headerLngIndex;
        rows = rows.slice(1);
    }

    let invalidCount = 0;
    rows.forEach((line, idx) => {
        const parts = splitCSVRow(line);
        const latValue = parts[latitudeIndex];
        const lngValue = parts[longitudeIndex];
        const lat = Number(latValue);
        const lng = Number(lngValue);
        if (!latValue || !lngValue || !isValidCoordinate([lng, lat])) {
            invalidCount++;
            return;
        }
        const code = encodeGeohash(lat, lng, precision);
        genResultsData.push({ id: idx + 1, lat, lng, code });
        genLayerGroup.addLayer(L.marker([lat, lng]).bindPopup(`
            <div class="font-mono text-xs p-1">
                <span class="text-amber-400 font-bold">${code}</span>
                <p class="text-slate-300">${lat}, ${lng}</p>
            </div>
        `));
    });

    if (genResultsData.length > 0) {
        const group = L.featureGroup(genLayerGroup.getLayers());
        genMap.fitBounds(group.getBounds(), { padding: [50, 50] });
    }

    status.textContent = genResultsData.length
        ? `Generated ${genResultsData.length} geohash${genResultsData.length === 1 ? '' : 'es'}${invalidCount ? `; skipped ${invalidCount} invalid row${invalidCount === 1 ? '' : 's'}` : ''}.`
        : 'No valid coordinate rows found. Check the latitude and longitude columns.';
    renderGeneratorResults();
}

function splitCSVRow(row) {
    return row.split(/,(?=(?:[^"]*"[^"]*")*[^"]*$)|\t|;/)
        .map(value => value.trim().replace(/^\uFEFF/, '').replace(/^"|"$/g, ''));
}

function renderGeneratorResults() {
    document.getElementById('gen-count-badge').innerText = `${genResultsData.length} Items`;
    const container = document.getElementById('gen-results-list');
    container.innerHTML = genResultsData.map(item => `
        <div class="p-2 bg-slate-900 rounded-lg border border-slate-800 flex justify-between items-center">
            <div>
                <span class="text-amber-400 font-bold">${item.code}</span>
                <div class="text-[10px] text-slate-400">${item.lat}, ${item.lng}</div>
            </div>
            <button type="button" aria-label="Copy ${item.code}" onclick="copyGeohash('${item.code}')" class="text-slate-400 hover:text-white p-1">
                <i class="fa-solid fa-copy"></i>
            </button>
        </div>
    `).join('');
}

function copyGeohash(code) {
    if (!navigator.clipboard) {
        document.getElementById('gen-status').textContent = 'Clipboard access is unavailable in this browser context.';
        return;
    }
    navigator.clipboard.writeText(code).then(
        () => { document.getElementById('gen-status').textContent = `Copied ${code}.`; },
        () => { document.getElementById('gen-status').textContent = 'Could not copy to the clipboard.'; }
    );
}

function handleGenCSVUpload(e) {
    const file = e.target.files[0];
    if (!file) return;

    const reader = new FileReader();
    reader.onerror = () => { document.getElementById('gen-status').textContent = 'Could not read the selected coordinate file.'; };
    reader.onload = function(evt) {
        const contents = String(evt.target.result);
        if (/\.(geojson|json)$/i.test(file.name)) {
            try {
                const geometries = collectGeoJSONGeometries(JSON.parse(contents));
                const points = getPointCoordinates(geometries);
                if (!points.length) throw new Error('No supported point or line coordinates were found.');
                document.getElementById('gen-coords-input').value =
                    points.map(([longitude, latitude]) => `${latitude}, ${longitude}`).join('\n');
            } catch (error) {
                document.getElementById('gen-status').textContent = `Coordinate file failed: ${error.message}`;
                e.target.value = '';
                return;
            }
        } else {
            document.getElementById('gen-coords-input').value = contents;
        }
        generateBatchGeohashes();
        e.target.value = '';
    };
    reader.readAsText(file);
}



/* =========================================================================
   6. POLYGON CONVERTER HANDLERS (CSV *Latitude,*Longitude & GeoJSON)
   ========================================================================= */
function loadDemoCambodiaPolygon() {
    const cambodiaPolygon = [[
        [104.484771, 11.48690407],
        [104.4848086, 11.48706874],
        [105.0000000, 11.55000000],
        [104.9000000, 12.00000000],
        [104.484771, 11.48690407]
    ]];
    processPolygonCoordinates([cambodiaPolygon], 'Demo boundary');
}

function handlePolyFileUpload(e) {
    const file = e.target.files[0];
    if (!file) return;

    const reader = new FileReader();
    reader.onerror = () => { document.getElementById('poly-status').textContent = 'Could not read the selected boundary file.'; };
    reader.onload = function(evt) {
        const content = String(evt.target.result);
        try {
            if (/\.csv$/i.test(file.name)) {
                parseCSVPolygon(content, file.name);
            } else {
                parseGeoJSONPolygon(JSON.parse(content), file.name);
            }
        } catch (error) {
            document.getElementById('poly-status').textContent = `Boundary conversion failed: ${error.message}`;
        } finally {
            e.target.value = '';
        }
    };
    reader.readAsText(file);
}

function parseCSVPolygon(csvText, sourceName = 'CSV boundary') {
    const lines = csvText.split(/\r?\n/).map(line => line.trim()).filter(Boolean);
    if (lines.length < 3) throw new Error('CSV must contain at least three boundary coordinates.');
    let rows = lines;
    let latitudeIndex = 0, longitudeIndex = 1;
    const columns = splitCSVRow(lines[0]).map(value => value.toLowerCase().replace(/[*_\s-]/g, ''));
    const headerLatIndex = columns.findIndex(value => ['lat', 'latitude', 'y'].includes(value));
    const headerLngIndex = columns.findIndex(value => ['lon', 'lng', 'longitude', 'x'].includes(value));
    if (headerLatIndex !== -1 && headerLngIndex !== -1) {
        latitudeIndex = headerLatIndex;
        longitudeIndex = headerLngIndex;
        rows = lines.slice(1);
    }

    const ring = [];
    rows.forEach((line, index) => {
        const parts = splitCSVRow(line);
        const latitudeValue = parts[latitudeIndex];
        const longitudeValue = parts[longitudeIndex];
        const latitude = Number(latitudeValue);
        const longitude = Number(longitudeValue);
        if (!latitudeValue || !longitudeValue || !isValidCoordinate([longitude, latitude])) {
            throw new Error(`Invalid coordinate on CSV row ${index + (rows === lines ? 1 : 2)}.`);
        }
        ring.push([longitude, latitude]);
    });
    processPolygonCoordinates([[ring]], sourceName);
}

function parseGeoJSONPolygon(geojson, sourceName = 'GeoJSON boundary') {
    const geometries = collectGeoJSONGeometries(geojson);
    const polygons = geometries.flatMap(getPolygonCoordinates);
    if (!polygons.length) throw new Error('GeoJSON must contain at least one Polygon or MultiPolygon.');
    processPolygonCoordinates(polygons, sourceName);
}

function normalizePolygonRings(polygon) {
    if (!Array.isArray(polygon) || !polygon.length) throw new Error('Polygon has no coordinate rings.');
    return polygon.map((inputRing, ringIndex) => {
        if (!Array.isArray(inputRing)) throw new Error('Polygon ring coordinates are invalid.');
        const ring = inputRing.map(coordinate => {
            if (!isValidCoordinate(coordinate)) throw new Error('Polygon contains an invalid longitude/latitude coordinate.');
            return [Number(coordinate[0]), Number(coordinate[1])];
        });
        if (ring.length > 1 && (ring[0][0] !== ring[ring.length - 1][0] || ring[0][1] !== ring[ring.length - 1][1])) {
            ring.push(ring[0].slice());
        }
        if (ring.length < 4) throw new Error(`Polygon ring ${ringIndex + 1} must contain at least three distinct points.`);
        return ring;
    });
}

function segmentsIntersect(a, b, c, d) {
    const cross = (p1, p2, p3) => (p2[0] - p1[0]) * (p3[1] - p1[1]) - (p2[1] - p1[1]) * (p3[0] - p1[0]);
    const onSegment = (p1, p2, p) =>
        p[0] >= Math.min(p1[0], p2[0]) - 1e-12 && p[0] <= Math.max(p1[0], p2[0]) + 1e-12 &&
        p[1] >= Math.min(p1[1], p2[1]) - 1e-12 && p[1] <= Math.max(p1[1], p2[1]) + 1e-12;
    const abC = cross(a, b, c), abD = cross(a, b, d);
    const cdA = cross(c, d, a), cdB = cross(c, d, b);
    if (((abC > 0 && abD < 0) || (abC < 0 && abD > 0)) &&
        ((cdA > 0 && cdB < 0) || (cdA < 0 && cdB > 0))) return true;
    return (Math.abs(abC) < 1e-12 && onSegment(a, b, c)) ||
        (Math.abs(abD) < 1e-12 && onSegment(a, b, d)) ||
        (Math.abs(cdA) < 1e-12 && onSegment(c, d, a)) ||
        (Math.abs(cdB) < 1e-12 && onSegment(c, d, b));
}

function polygonIntersectsCell(rings, minLng, minLat, maxLng, maxLat) {
    const corners = [
        [minLng, minLat], [maxLng, minLat], [maxLng, maxLat], [minLng, maxLat]
    ];
    if (corners.some(corner => isPointInPolygon(corner, rings))) return true;
    const cellEdges = corners.map((corner, index) => [corner, corners[(index + 1) % corners.length]]);
    for (const ring of rings) {
        for (let index = 0; index < ring.length - 1; index++) {
            const point = ring[index];
            if (point[0] >= minLng && point[0] <= maxLng && point[1] >= minLat && point[1] <= maxLat) return true;
            if (cellEdges.some(edge => segmentsIntersect(ring[index], ring[index + 1], edge[0], edge[1]))) return true;
        }
    }
    return false;
}

function getPolygonGeohashCover(inputPolygon, precision) {
    if (!Number.isInteger(precision) || precision < 1 || precision > 12) {
        throw new RangeError('Geohash precision must be between 1 and 12.');
    }
    const rings = normalizePolygonRings(inputPolygon);
    const anchor = rings[0][0][0];
    const unwrapped = rings.map((ring, ringIndex) => {
        const shift = ringIndex === 0 ? 0 : 360 * Math.round((anchor - ring[0][0]) / 360);
        const points = [];
        ring.forEach((point, index) => {
            let longitude = point[0] + shift;
            if (index > 0) {
                while (longitude - points[index - 1][0] > 180) longitude -= 360;
                while (longitude - points[index - 1][0] < -180) longitude += 360;
            }
            points.push([longitude, point[1]]);
        });
        return points;
    });
    if (unwrapped.slice(1).some(ring => !isPointInRing(ring[0], unwrapped[0]))) {
        throw new Error('Polygon holes must be inside the outer boundary.');
    }
    const bounds = unwrapped.flat().reduce((result, point) => ({
        minLng: Math.min(result.minLng, point[0]),
        maxLng: Math.max(result.maxLng, point[0]),
        minLat: Math.min(result.minLat, point[1]),
        maxLat: Math.max(result.maxLat, point[1])
    }), { minLng: Infinity, maxLng: -Infinity, minLat: Infinity, maxLat: -Infinity });
    const totalBits = precision * 5;
    const longitudeBits = Math.ceil(totalBits / 2);
    const latitudeBits = Math.floor(totalBits / 2);
    const longitudeStep = 360 / (2 ** longitudeBits);
    const latitudeStep = 180 / (2 ** latitudeBits);
    const columnCount = 2 ** longitudeBits;
    const rowCount = 2 ** latitudeBits;
    const minColumn = Math.floor((bounds.minLng + 180) / longitudeStep);
    const maxColumn = Math.floor((bounds.maxLng + 180) / longitudeStep);
    const minRow = Math.max(0, Math.floor((bounds.minLat + 90) / latitudeStep));
    const maxRow = Math.min(rowCount - 1, Math.floor((bounds.maxLat + 90) / latitudeStep));
    const candidateCount = (maxColumn - minColumn + 1) * (maxRow - minRow + 1);
    if (!Number.isFinite(candidateCount) || candidateCount > 50000) {
        throw new Error('This boundary covers too many candidate cells. Choose a lower precision or a smaller area.');
    }

    const results = new Map();
    for (let row = minRow; row <= maxRow; row++) {
        const cellMinLat = -90 + row * latitudeStep;
        const cellMaxLat = cellMinLat + latitudeStep;
        for (let column = minColumn; column <= maxColumn; column++) {
            const cellMinLng = -180 + column * longitudeStep;
            const cellMaxLng = cellMinLng + longitudeStep;
            if (!polygonIntersectsCell(unwrapped, cellMinLng, cellMinLat, cellMaxLng, cellMaxLat)) continue;
            const wrappedColumn = ((column % columnCount) + columnCount) % columnCount;
            const wrappedLongitude = -180 + (wrappedColumn + 0.5) * longitudeStep;
            const code = encodeGeohash(cellMinLat + latitudeStep / 2, wrappedLongitude, precision);
            if (!results.has(code)) {
                results.set(code, { code, ...decodeGeohash(code) });
                if (results.size > MAX_RESULT_ITEMS) {
                    throw new Error(`The boundary produces more than ${MAX_RESULT_ITEMS.toLocaleString()} cells. Choose a lower precision or a smaller area.`);
                }
            }
        }
    }
    return Array.from(results.values());
}

function processPolygonCoordinates(polygons, sourceName = 'Boundary') {
    const precision = Number(document.getElementById('poly-precision').value);
    const normalized = polygons.map(normalizePolygonRings);
    const cells = new Map();
    normalized.forEach(polygon => getPolygonGeohashCover(polygon, precision)
        .forEach(item => {
            cells.set(item.code, item);
            if (cells.size > MAX_RESULT_ITEMS) {
                throw new Error(`The boundary produces more than ${MAX_RESULT_ITEMS.toLocaleString()} cells. Choose a lower precision or a smaller area.`);
            }
        }));
    if (!cells.size) throw new Error('The boundary does not intersect any geohash cells.');

    polyLayerGroup.clearLayers();
    polyResultsData = Array.from(cells.values());
    const polygonLayers = normalized.map(rings => {
        const layer = L.polygon(rings.map(ring => ring.map(([longitude, latitude]) => [latitude, longitude])), {
            color: '#818cf8',
            weight: 2,
            fillColor: '#6366f1',
            fillOpacity: 0.12
        });
        polyLayerGroup.addLayer(layer);
        return layer;
    });
    polyResultsData.forEach(item => {
        polyLayerGroup.addLayer(L.rectangle([[item.latMin, item.lonMin], [item.latMax, item.lonMax]], {
            color: '#00b14f',
            weight: 1,
            fillColor: '#00b14f',
            fillOpacity: 0.22
        }));
    });
    polyMap.fitBounds(L.featureGroup(polygonLayers).getBounds(), { padding: [50, 50] });
    document.getElementById('poly-count-badge').innerText = `${polyResultsData.length} Grid Cells`;
    document.getElementById('poly-status').textContent =
        `${sourceName}: ${polyResultsData.length} intersecting cells at precision ${precision}.`;
    document.getElementById('poly-results-container').innerHTML = polyResultsData.map(item => `
        <div class="p-1.5 bg-slate-900 rounded border border-slate-800 flex justify-between">
            <span class="text-indigo-400 font-bold">${item.code}</span>
            <span class="text-[10px] text-slate-400">${item.latitude}, ${item.longitude}</span>
        </div>
    `).join('');
}

/* =========================================================================
   7. EXPORT ENGINE & THEME TOGGLE
   ========================================================================= */
function exportSearchGeoJSON() {
    downloadFile(
        JSON.stringify(geohashesToFeatureCollection(searchResultsData), null, 2),
        'geohash_search_results.geojson',
        'application/geo+json'
    );
}

function geohashesToFeatureCollection(geohashes) {
    return {
        type: 'FeatureCollection',
        features: geohashes.map(item => ({
            type: 'Feature',
            properties: {
                geohash: item.code,
                latitude: item.latitude,
                longitude: item.longitude,
                lat_min: item.latMin,
                lat_max: item.latMax,
                lon_min: item.lonMin,
                lon_max: item.lonMax
            },
            geometry: {
                type: 'Polygon',
                coordinates: [[
                    [item.lonMin, item.latMin],
                    [item.lonMax, item.latMin],
                    [item.lonMax, item.latMax],
                    [item.lonMin, item.latMax],
                    [item.lonMin, item.latMin]
                ]]
            }
        }))
    };
}

function exportSearchCSV() {
    let csv = "geohash,latitude,longitude,lat_min,lat_max,lon_min,lon_max\n";
    searchResultsData.forEach(d => {
        csv += `${d.code},${d.latitude},${d.longitude},${d.latMin},${d.latMax},${d.lonMin},${d.lonMax}\n`;
    });
    downloadFile(csv, 'geohash_search_results.csv', 'text/csv');
}

function exportPolyGeoJSON() {
    downloadFile(
        JSON.stringify(geohashesToFeatureCollection(polyResultsData), null, 2),
        'polygon_geohashes.geojson',
        'application/geo+json'
    );
}

function exportPolyCSV() {
    let csv = "geohash,latitude,longitude,lat_min,lat_max,lon_min,lon_max\n";
    polyResultsData.forEach(d => {
        csv += `${d.code},${d.latitude},${d.longitude},${d.latMin},${d.latMax},${d.lonMin},${d.lonMax}\n`;
    });
    downloadFile(csv, 'polygon_geohashes.csv', 'text/csv');
}

function downloadFile(content, fileName, contentType) {
    const a = document.createElement("a");
    const file = new Blob([content], { type: contentType });
    a.href = URL.createObjectURL(file);
    a.download = fileName;
    a.click();
    URL.revokeObjectURL(a.href);
}

function toggleAppTheme() {
    const body = document.getElementById('app-body');
    const btn = document.getElementById('theme-btn');
    if (body.classList.contains('dark')) {
        body.classList.remove('dark');
        body.classList.add('light', 'bg-slate-100', 'text-slate-900');
        btn.innerHTML = `<i class="fa-solid fa-moon"></i>`;
    } else {
        body.classList.remove('light', 'bg-slate-100', 'text-slate-900');
        body.classList.add('dark', 'bg-slate-950', 'text-slate-100');
        btn.innerHTML = `<i class="fa-solid fa-sun"></i>`;
    }
}
